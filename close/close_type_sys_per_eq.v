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


(* MOVE to per_ceq_bar *)
Lemma two_computes_to_valc_ceq_bar_mkc_equality {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2 # ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_equality in q; repnd; dands; spcast; auto.
Qed.

(* MOVE to per_ceq_bar *)
Lemma two_computes_to_valc_ceq_bar_mkc_equality1 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

(* MOVE to per_ceq_bar *)
Lemma two_computes_to_valc_ceq_bar_mkc_equality2 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

(* MOVE to per_ceq_bar *)
Lemma two_computes_to_valc_ceq_bar_mkc_equality3 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2 A B,
    T ==b==>(bar1) (mkc_equality a1 b1 A)
    -> T ==b==>(bar2) (mkc_equality a2 b2 B)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib A B).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_equality in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

(* MOVE to per_ceq_bar *)
Lemma cequivc_type_sys_props_implies_equal_types {o} :
  forall ts lib (A B C : @CTerm o) eqa,
    type_sys_props ts lib A B eqa
    -> ccequivc_ext lib A C
    -> ts lib A C eqa.
Proof.
  introv tsp ceq.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  pose proof (tyvr A C) as q; repeat (autodimp q hyp).
Qed.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 (close ts) lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => close ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp cl ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; exrepnd.
  simpl in *; exrepnd.
  pose proof (tsp lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply tyvrt in w; tcsp.
  eapply w in h; clear w.
  apply uv in h; auto.
Qed.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext {o} :
  forall lib (bar : BarLib lib) (a b : @CTerm o),
    all_in_bar bar (fun lib => ccequivc lib a b)
    -> all_in_bar bar (fun lib => ccequivc_ext lib a b).
Proof.
  introv h br ext ext'.
  apply (h lib' br lib'1); eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext : slow.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_type_sys_props4_implies_term_equality_respecting {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa).
Proof.
  introv h b ext.
  pose proof (h lib' b lib'0 ext) as h; simpl in h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_term_equality_respecting : slow.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_type_sys_props4_implies_term_equality_symmetric {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> term_equality_symmetric eqa.
Proof.
  introv h.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (h lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_term_equality_symmetric : slow.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_type_sys_props4_implies_term_equality_transitive {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> term_equality_transitive eqa.
Proof.
  introv h.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (h lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_term_equality_transitive : slow.

(* MOVE to per_ceq_bar *)
Lemma implies_computes_to_valc_ceq_bar_intersect_bars_left {o} :
  forall lib (bar1 bar2 : @BarLib o lib) T v,
    T ==b==>(bar1) v
    -> T ==b==>(intersect_bars bar1 bar2) v.
Proof.
  introv comp br ext; simpl in *; exrepnd.
  apply (comp lib1 br0 lib'0); eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_ceq_bar_intersect_bars_left : slow.

(* MOVE to per_ceq_bar *)
Lemma implies_computes_to_valc_ceq_bar_intersect_bars_right {o} :
  forall lib (bar1 bar2 : @BarLib o lib) T v,
    T ==b==>(bar2) v
    -> T ==b==>(intersect_bars bar1 bar2) v.
Proof.
  introv comp br ext; simpl in *; exrepnd.
  apply (comp lib2 br2 lib'0); eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_ceq_bar_intersect_bars_right : slow.

(* MOVE to per_ceq_bar *)
Lemma implies_iff_per_eq_eq {o} :
  forall lib (bar : @BarLib o lib) a1 a2 b1 b2 eqa eqb,
    (eqa <=2=> eqb)
    -> all_in_bar bar (fun lib => a1 ~=~(lib) b1)
    -> all_in_bar bar (fun lib => a2 ~=~(lib) b2)
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa)
    -> (per_eq_eq lib a1 a2 eqa) <=2=> (per_eq_eq lib b1 b2 eqb).
Proof.
  introv eqeq alla allb tes tet ter; introv.
  unfold per_eq_eq, per_eq_eq1; split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv b ext; simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd.
    dands; auto.
    apply eqeq; auto.

    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in alla.
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in allb.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0) as h; simpl in h; autodimp h hyp; eauto 3 with slow; spcast.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow; spcast.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0) as z; simpl in z; autodimp z hyp; eauto 3 with slow; spcast.
    eapply eqorceq_commutes;eauto; right; auto.

  - exists (intersect_bars bar bar0).
    introv b ext; simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd.
    dands; auto.
    apply eqeq in q; auto.

    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in alla.
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in allb.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0) as h; simpl in h; autodimp h hyp; eauto 3 with slow; spcast.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow; spcast.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0) as z; simpl in z; autodimp z hyp; eauto 3 with slow; spcast.
    eapply eqorceq_commutes;eauto; right; apply ccequivc_ext_sym; auto.
Qed.
Hint Resolve implies_iff_per_eq_eq : slow.

(* MOVE to per_ceq_bar *)
Lemma implies_all_in_bar_eqorceq_trans_ccequivc {o} :
  forall lib (bar : @BarLib o lib) a b c eqa,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa)
    -> all_in_bar bar (fun lib => a ~=~(lib) b)
    -> all_in_bar bar (fun lib => eqorceq lib eqa b c)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a c).
Proof.
  introv tes tet ter alla allb br ext.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in alla.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  pose proof (ter lib' br lib'0 ext) as ter; simpl in *.
  eapply eqorceq_trans; eauto.
  right; eauto.
Qed.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_eqorceq_eq_term_equals {o} :
  forall lib (bar : @BarLib o lib) eq1 eq2 a b,
    (eq1 <=2=> eq2)
    -> all_in_bar bar (fun lib => eqorceq lib eq1 a b)
    -> all_in_bar bar (fun lib => eqorceq lib eq2 a b).
Proof.
  introv eqiff alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  eapply eqorceq_eq_term_equals;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve all_in_bar_eqorceq_eq_term_equals : slow.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_eqorceq_eq_term_equals2 {o} :
  forall lib (bar : @BarLib o lib) eq1 eq2 a b,
    (eq2 <=2=> eq1)
    -> all_in_bar bar (fun lib => eqorceq lib eq1 a b)
    -> all_in_bar bar (fun lib => eqorceq lib eq2 a b).
Proof.
  introv eqiff alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  eapply eqorceq_eq_term_equals;[|eauto]; auto.
Qed.
Hint Resolve all_in_bar_eqorceq_eq_term_equals2 : slow.

(* MOVE to per_ceq_bar *)
Lemma ccequivc_ext_refl {o} :
  forall lib (a : @CTerm o), ccequivc_ext lib a a.
Proof.
  introv ext; spcast; auto.
Qed.
Hint Resolve ccequivc_ext_refl : slow.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_type_sys_props4_implies_type_equality_respecting_trans2 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib A1 B1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa1).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply tyvrt in w; tcsp.
  eapply w in h; clear w.
  applydup uv in h.

  pose proof (dum A1 A1 B2 eqa1 eqa2) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

(* MOVE to per_ceq_bar *)
Ltac rename_hyp_with oldname newname :=
  match goal with
  | [ H : context[oldname] |- _ ] => rename H into newname
  end.

(* MOVE to per_ceq_bar *)
Lemma type_sys_props_ts_refl_left {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A A eqa).
Proof.
  introv alla br ext.
  pose proof (alla lib' br lib'0 ext) as q; simpl in q.

  apply type_sys_prop4_implies_type_sys_props3 in q.
  apply type_sys_props_iff_type_sys_props3 in q.
  apply type_sys_props_ts_refl in q; tcsp.
Qed.
Hint Resolve type_sys_props_ts_refl_left : slow.

(* MOVE to per_ceq_bar *)
Lemma type_sys_props_ts_refl_right {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib B B eqa).
Proof.
  introv alla br ext.
  pose proof (alla lib' br lib'0 ext) as q; simpl in q.

  apply type_sys_prop4_implies_type_sys_props3 in q.
  apply type_sys_props_iff_type_sys_props3 in q.
  apply type_sys_props_ts_refl in q; tcsp.
Qed.
Hint Resolve type_sys_props_ts_refl_right : slow.

(* MOVE to per_ceq_bar *)
Lemma eqorceq_refl {o} :
  forall lib eqa (a : @CTerm o),
    eqorceq lib eqa a a.
Proof.
  introv; right; eauto 3 with slow.
Qed.
Hint Resolve eqorceq_refl : slow.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_eqorceq_refl {o} :
  forall lib (bar : @BarLib o lib) eqa a,
    all_in_bar bar (fun lib => eqorceq lib eqa a a).
Proof.
  introv br ext; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_eqorceq_refl : slow.

(* MOVE to per_ceq_bar *)
Lemma eqorceq_implies_iff_per_eq_eq {o} :
  forall lib (bar : @BarLib o lib) a1 a2 b1 b2 eqa eqb,
    (eqa <=2=> eqb)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a1 b1)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a2 b2)
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa)
    -> (per_eq_eq lib a1 a2 eqa) <=2=> (per_eq_eq lib b1 b2 eqb).
Proof.
  introv eqeq alla allb tes tet ter; introv.
  unfold per_eq_eq, per_eq_eq1; split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv b ext; simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd.
    dands; auto.
    apply eqeq; auto.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0) as h; simpl in h; autodimp h hyp; eauto 3 with slow; spcast.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow; spcast.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0) as z; simpl in z; autodimp z hyp; eauto 3 with slow; spcast.
    eapply eqorceq_commutes;eauto; right; auto.

  - exists (intersect_bars bar bar0).
    introv b ext; simpl in *; exrepnd.
    pose proof (h0 lib2 b4 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; repnd.
    dands; auto.
    apply eqeq in q; auto.

    pose proof (alla lib1 b0) as h.
    pose proof (h lib'0) as h; simpl in h; autodimp h hyp; eauto 3 with slow; spcast.

    pose proof (allb lib1 b0) as w.
    pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow; spcast.

    pose proof (ter lib1 b0) as z.
    pose proof (z lib'0) as z; simpl in z; autodimp z hyp; eauto 3 with slow; spcast.
    eapply eqorceq_commutes;eauto; apply eqorceq_sym; auto.
Qed.
Hint Resolve eqorceq_implies_iff_per_eq_eq : slow.

(* MOVE to per_ceq_bar *)
Lemma type_equality_respecting_trans_per_eq_bar_implies {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T' a b A a' b' A',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) (mkc_equality a b A)
    -> T' ==b==>(bar) (mkc_equality a' b' A')
    -> type_equality_respecting_trans (per_eq_bar (close ts)) lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply CL_eq.
  eapply trans; eauto.
  repndors; subst.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.
Qed.

(* MOVE to per_ceq_bar *)
Lemma sub_type_system_implies_type_equality_respecting_trans {o} :
  forall (ts : cts(o)) lib (T1 T2 : @CTerm o),
    type_symmetric ts
    -> type_transitive ts
    -> type_value_respecting ts
    -> type_equality_respecting_trans ts lib T1 T2.
Proof.
  introv tys tyt tyvr.
  introv h ceq q; repndors; subst.

  - pose proof (tyvr lib T3 T1 eq') as w.
    apply ccequivc_ext_sym in ceq.
    repeat (autodimp w hyp);[eapply tyt;[eauto|apply tys;auto] |].
    apply tys in w.
    eapply tyt; eauto.

  - pose proof (tyvr lib T3 T2 eq') as w.
    apply ccequivc_ext_sym in ceq.
    repeat (autodimp w hyp);[eapply tyt;[eauto|apply tys;auto] |].
    apply tys in w.
    eapply tyt; eauto.
Qed.

(* MOVE to per_ceq_bar *)
Lemma type_system_implies_all_in_bar_sym {o} :
  forall lib (bar : @BarLib o lib) ts A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib B A eqa).
Proof.
  introv tsts alla br ext.
  pose proof (alla lib' br lib'0 ext) as q; simpl in q.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_implies_all_in_bar_sym : slow.

(* MOVE to per_ceq_bar *)
Lemma type_system_implies_all_in_bar_trans {o} :
  forall lib (bar : @BarLib o lib) ts A B C eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib B C eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa).
Proof.
  introv tsts alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_implies_all_in_bar_trans : slow.

(* MOVE to per_ceq_bar *)
Lemma type_system_implies_all_in_bar_eqorceq_sym {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) eqa a b A B,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a b)
    -> all_in_bar bar (fun lib => eqorceq lib eqa b a).
Proof.
  introv tsts alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
  apply eqorceq_sym; eauto.
Qed.
Hint Resolve type_system_implies_all_in_bar_eqorceq_sym : slow.

(* MOVE to per_ceq_bar *)
Lemma type_system_all_in_bar_ts_implies_term_equality_symmetric {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> term_equality_symmetric eqa.
Proof.
  introv tsts alla.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (alla lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_all_in_bar_ts_implies_term_equality_symmetric : slow.

(* MOVE to per_ceq_bar *)
Lemma type_system_all_in_bar_ts_implies_term_equality_transitive {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> term_equality_transitive eqa.
Proof.
  introv tsts alla.
  pose proof (bar_non_empty bar) as b; exrepnd.
  pose proof (alla lib') as h; autodimp h hyp.
  pose proof (h lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_all_in_bar_ts_implies_term_equality_transitive : slow.

(* MOVE to per_ceq_bar *)
Lemma type_system_all_in_bar_ts_implies_term_equality_respecting {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) A B eqa,
    type_system ts
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa).
Proof.
  introv tsts alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  onedts uv tye tys tyt tyvr tes tet tevr; eauto.
Qed.
Hint Resolve type_system_all_in_bar_ts_implies_term_equality_respecting : slow.

(* MOVE to per_ceq_bar *)
Lemma type_system_implies_type_equality_respecting_trans3 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    type_system ts
    -> all_in_bar bar1 (fun lib => ts lib A1 A2 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 B1 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib A2 B2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B1 eqa1).
Proof.
  introv tsp ts1 ts2 ceq br ext; simpl in *; exrepnd.

  pose proof (ts1 lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (ts2 lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  onedts uv tye tys tyt tyvr tes tet tevr.

  eapply uniquely_valued_trans2;auto;[exact q|].
  eapply uniquely_valued_trans2;auto;[|exact h].
  eapply type_reduces_to_symm2;auto;eauto.
Qed.
Hint Resolve type_system_implies_type_equality_respecting_trans3 : slow.

(* MOVE to per_ceq_bar *)
Lemma type_system_implies_type_equality_respecting_trans4 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    type_system ts
    -> all_in_bar bar1 (fun lib => ts lib A1 A2 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib B2 B1 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib A2 B2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp ts1 ts2 ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; simpl in b; exrepnd.

  pose proof (ts1 lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (ts2 lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  onedts uv tye tys tyt tyvr tes tet tevr.
  eapply uniquely_valued_eq2; try (exact q); auto.
  eapply uniquely_valued_trans2;auto;[|exact h].
  apply type_system_type_symm;auto.
  eapply type_reduces_to_symm2;auto;eauto.
  apply ccequivc_ext_sym;auto.
Qed.
Hint Resolve type_system_implies_type_equality_respecting_trans4 : slow.

(* MOVE to per_ceq_bar *)
Lemma implies_all_in_bar_eqorceq {o} :
  forall lib (bar1 bar2 : @BarLib o lib) a1 b1 a2 b2 eqa1 eqa2,
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> all_in_bar bar1 (fun lib => term_equality_respecting lib eqa1)
    -> all_in_bar bar1 (fun lib => eqorceq lib eqa1 a1 b1)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => b1 ~=~(lib) a2)
    -> all_in_bar bar2 (fun lib => eqorceq lib eqa2 a2 b2)
    -> (eqa1 <=2=> eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => eqorceq lib eqa1 a1 b2).
Proof.
  introv tes1 tet1 ter1 alla allb allc eqiff br ext; simpl in *; exrepnd.
  pose proof (alla lib1 br0 lib'0) as alla; simpl in alla; autodimp alla hyp; eauto 3 with slow.
  pose proof (allc lib2 br2 lib'0) as allc; simpl in allc; autodimp allc hyp; eauto 3 with slow.
  apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in allb.
  pose proof (allb lib') as allb; simpl in allb; autodimp allb hyp;[exists lib1 lib2; dands; auto|].
  pose proof (allb lib'0 ext) as allb; simpl in allb.

  pose proof (ter1 lib1 br0 lib'0) as ter1; autodimp ter1 hyp; eauto 3 with slow; simpl in *.

  eapply eqorceq_trans;auto;[exact alla|].
  eapply eqorceq_trans;auto;[right;exact allb|].
  eapply eqorceq_eq_term_equals;[exact eqiff|];auto.
Qed.
Hint Resolve implies_all_in_bar_eqorceq : slow.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 (close ts) lib B1 A1 eqa1)
    -> all_in_bar bar2 (fun lib => close ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> eqa1 <=2=> eqa2.
Proof.
  introv tsp cl ceq; simpl in *; exrepnd.

  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as b; exrepnd.
  simpl in *; exrepnd.
  pose proof (tsp lib1 b1 lib') as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 b2 lib') as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib') as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  unfold type_equality_respecting_trans in tyvrt.
  apply (tyvrt A1 A2 B2 eqa2) in w; auto;[].
  pose proof (dum A1 B1 B2 eqa1 eqa2) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.
Qed.

(* MOVE to per_ceq_bar *)
Lemma all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans2 {o} :
  forall ts lib (bar1 bar2 : @BarLib o lib) A1 B1 A2 B2 eqa1 eqa2,
    all_in_bar bar1 (fun lib => type_sys_props4 ts lib B1 A1 eqa1)
    -> all_in_bar bar2 (fun lib => ts lib A2 B2 eqa2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc_ext lib A1 A2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ts lib A1 B2 eqa1).
Proof.
  introv tsp cl ceq br ext; simpl in *; exrepnd.

  pose proof (tsp lib1 br0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q.
  pose proof (cl lib2 br2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  pose proof (ceq lib') as w; simpl in w; autodimp w hyp;[eexists; eexists; eauto|].
  pose proof (w lib'0) as w; simpl in w; autodimp w hyp; eauto 3 with slow.

  clear tsp cl ceq.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  apply (tyvrt A1 A2 B2 eqa2) in w; auto;[].
  pose proof (dum A1 B1 B2 eqa1 eqa2) as q; repeat (autodimp q hyp); repnd.
  apply uv in q; auto.

  pose proof (dum A1 A1 B2 eqa1 eqa2) as z; repeat (autodimp z hyp); tcsp.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma all_in_bar_type_sys_props4_implies_ts_sym {o} :
  forall ts lib (bar : BarLib lib) (A B C : @CTerm o) eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => ts lib A C eqa)
    -> all_in_bar bar (fun lib => ts lib C A eqa).
Proof.
  introv alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in alla.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in allb.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tygs; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_implies_ts_sym : slow.

(* MOVE to per_ceq_bar *)
Lemma implies_all_in_bar_eqorceq_sym {o} :
  forall lib (bar : @BarLib o lib) (ts : cts(o)) eqa a b A B,
    term_equality_symmetric eqa
    -> all_in_bar bar (fun lib => ts lib A B eqa)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a b)
    -> all_in_bar bar (fun lib => eqorceq lib eqa b a).
Proof.
  introv tes alla allb br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  pose proof (allb lib' br lib'0 ext) as allb; simpl in *.
  apply eqorceq_sym; eauto.
Qed.
Hint Resolve implies_all_in_bar_eqorceq_sym : slow.

(* MOVE to per_ceq_bar *)
Lemma eq_term_equals_preserves_term_equality_symmetric {o} :
  forall (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_symmetric eqa1
    -> term_equality_symmetric eqa2.
Proof.
  introv eqiff tes ee.
  apply eqiff in ee; apply eqiff; tcsp.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_symmetric : slow.

(* MOVE to per_ceq_bar *)
Lemma eq_term_equals_preserves_term_equality_transitive {o} :
  forall (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_transitive eqa1
    -> term_equality_transitive eqa2.
Proof.
  introv eqiff tet ee1 ee2.
  apply eqiff in ee1; apply eqiff in ee2; apply eqiff.
  eapply tet; eauto.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_transitive : slow.

(* MOVE to per_ceq_bar *)
Lemma eq_term_equals_preserves_all_in_bar_term_equality_respecting {o} :
  forall lib (bar : BarLib lib) (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa1)
    -> all_in_bar bar (fun lib => term_equality_respecting lib eqa2).
Proof.
  introv eqiff alla br ext ee ceq.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in alla.
  apply eqiff in ee; apply eqiff; tcsp.
Qed.
Hint Resolve eq_term_equals_preserves_all_in_bar_term_equality_respecting : slow.

(* MOVE to per_ceq_bar *)
Hint Resolve eq_term_equals_sym : slow.

(* MOVE to per_ceq_bar *)
Hint Resolve all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext : slow.



(*Lemma per_eq_bar_type_symmetric {p} :
  forall (ts : cts(p)),
    type_system ts
    -> type_symmetric (per_eq_bar ts).
Proof.
  introv tsts per.
  unfold per_eq_bar in *; exrepnd.
  exists B A b1 b2 a1 a2 eqa; dands; auto.

  { exists bar; dands; eauto 3 with slow. }

  { eapply eq_term_equals_trans;[eauto|].
    eapply eqorceq_implies_iff_per_eq_eq; eauto; eauto 3 with slow. }
Qed.
Hint Resolve per_eq_bar_type_symmetric : slow.

Lemma per_eq_bar_type_transitive {o} :
  forall (ts : cts(o)),
    type_system ts
    -> type_transitive (per_eq_bar ts).
Proof.
  introv tsts per1 per2.
  unfold per_eq_bar in *; exrepnd.

  pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar0 bar T2 b0 b3 a1 a2 B0 A) as q1.
  repeat (autodimp q1 hyp).
  pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar0 bar T2 b0 b3 a1 a2 B0 A) as q2.
  repeat (autodimp q2 hyp).
  pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar0 bar T2 b0 b3 a1 a2 B0 A) as q3.
  repeat (autodimp q3 hyp).
  pose proof (type_system_implies_type_equality_respecting_trans4 ts lib bar0 bar A0 B B0 A eqa0 eqa) as q4.
  repeat (autodimp q4 hyp).

  exists A0 B a0 a3 b1 b2 eqa0; dands; auto.

  {
    exists (intersect_bars bar0 bar); dands; eauto 3 with slow;
      try (eapply implies_all_in_bar_eqorceq;eauto; eauto 3 with slow).
  }
Qed.
Hint Resolve per_eq_bar_type_transitive : slow.*)



Lemma close_type_system_eq {p} :
  forall lib (bar : BarLib lib) (ts : cts(p))
         T T' (eq : per) A B a1 a2 b1 b2 eqa,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) (mkc_equality a1 a2 A)
    -> T' ==b==>(bar) (mkc_equality b1 b2 B)
    -> all_in_bar bar (fun lib => close ts lib A B eqa)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a1 b1)
    -> all_in_bar bar (fun lib => eqorceq lib eqa a2 b2)
    -> (eq <=2=> (per_eq_eq lib a1 a2 eqa))
    -> per_eq_bar (close ts) lib T T' eq
    -> all_in_bar bar (fun lib => type_sys_props4 (close ts) lib A B eqa)
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tsts dou mon c1 c2 X1 eos1 eos2 eqiff per; introv IHX1.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_eq".
      clear per.
      allunfold @per_eq_bar; sp.
      unfold eq_term_equals; sp.
      spcast; allrw.

      pose proof (all_in_bar_type_sys_props4_implies_type_equality_respecting_trans ts lib bar bar0 A B A0 B0 eqa eqa0) as q.
      repeat (autodimp q hyp);
        [apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext;
         eapply two_computes_to_valc_ceq_bar_mkc_equality3; eauto|];[].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as h1.
      repeat (autodimp h1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as h2.
      repeat (autodimp h2 hyp);[].

      eapply implies_iff_per_eq_eq; eauto 3 with slow.

  + SCase "type_symmetric".
    clear per.
    repdors; subst; dclose_lr.
    allunfold @per_eq_bar; exrepd.
    apply CL_eq; unfold per_eq_bar.

    pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as h1.
    repeat (autodimp h1 hyp);[].
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as h2.
    repeat (autodimp h2 hyp);[].
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as h3.
    repeat (autodimp h3 hyp);[].

    pose proof (all_in_bar_type_sys_props4_implies_type_equality_respecting_trans ts lib bar bar0 A B A0 B0 eqa eqa0) as q.
    repeat (autodimp q hyp);
      [apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext; eauto|];[].

    (* 1 *)
    exists A B0 a1 a2 b0 b3 eqa; sp; spcast; sp.

    {
      exists (intersect_bars bar bar0).
      dands; auto; eauto 3 with slow.

      - eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans2; eauto; eauto 3 with slow.

      - eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.

      - eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
    }

    {
      eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|].
      eapply eq_term_equals_trans;[eauto|].
      apply eq_term_equals_sym.
      eapply implies_iff_per_eq_eq; eauto 3 with slow.
    }

  + SCase "type_value_respecting".
    clear per.
    repdors; subst; apply CL_eq; allunfold @per_eq_bar; sp.

    {
      rename_hyp_with @ccequivc_ext ceq.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists A A a1 a2 a1 a2 eqa; dands; auto.
      exists bar; dands; auto; eauto 3 with slow.
    }

    {
      rename_hyp_with @ccequivc_ext ceq.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists B B b1 b2 b1 b2 eqa; dands; auto.

      - exists bar; dands; auto; eauto 3 with slow.

      - eapply eq_term_equals_trans;[eauto|].
        eapply eqorceq_implies_iff_per_eq_eq; eauto 3 with slow.
    }

  + SCase "type_value_respecting_trans".
    clear per.
    eapply type_equality_respecting_trans_per_eq_bar_implies; eauto.
    introv e ceq cl.
    repndors; subst; allunfold @per_eq_bar; exrepnd.

    {
      dup cl1 as cl'.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in cl';[|apply ccequivc_ext_sym;eauto].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as h1.
      repeat (autodimp h1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as h2.
      repeat (autodimp h2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as h3.
      repeat (autodimp h3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in h3.
      pose proof (all_in_bar_type_sys_props4_implies_type_equality_respecting_trans ts lib bar bar0 A B A0 B0 eqa eqa0) as h4.
      repeat (autodimp h4 hyp);[].

      exists A B0 a1 a2 b0 b3 eqa; dands; auto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow.
        { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans2; eauto 3 with slow. }
        { eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto 3 with slow. }
        { eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto 3 with slow. }

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym;eauto 3 with slow.
        eapply implies_iff_per_eq_eq; eauto; eauto 3 with slow.
    }

    {
      dup cl1 as cl'.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in cl';[|apply ccequivc_ext_sym;eauto].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T' b1 b2 a0 a3 B A0) as h1.
      repeat (autodimp h1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T' b1 b2 a0 a3 B A0) as h2.
      repeat (autodimp h2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T' b1 b2 a0 a3 B A0) as h3.
      repeat (autodimp h3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in h3.
      pose proof (all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans ts lib bar bar0 B A A0 B0 eqa eqa0) as h4.
      repeat (autodimp h4 hyp);[].

      exists B B0 b1 b2 b0 b3 eqa; dands; auto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow.
        { eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto 3 with slow. }
        { eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto 3 with slow. }
        { eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto 3 with slow. }

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym;eauto 3 with slow.
        eapply implies_iff_per_eq_eq; eauto; eauto 3 with slow.
    }

  + SCase "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff.
    unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
    exists bar0.
    introv br ext.
    pose proof (ee0 lib' br lib'0 ext) as ee0; simpl in ee0.
    repnd; dands; auto.

  + SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff.
    unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
    exists (intersect_bars bar1 bar0).
    introv br ext; simpl in *; exrepnd.
    pose proof (ee2 lib1 br0 lib'0) as ee2; simpl in ee2; autodimp ee2 hyp; eauto 3 with slow.
    pose proof (ee0 lib2 br2 lib'0) as ee0; simpl in ee0; autodimp ee0 hyp; eauto 3 with slow.
    repnd; dands; auto.

  + SCase "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.
    unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
    exists bar0.
    introv br ext.
    pose proof (ee0 lib' br lib'0 ext) as ee0; simpl in ee0.
    repnd; dands; auto.
    pose proof (ceq lib'0) as ceq; simpl in ceq; autodimp ceq hyp; eauto 3 with slow.
    spcast; eapply cequivc_axiom; eauto.

  + SCase "type_gsymmetric".
    split; introv cl; dclose_lr; apply CL_eq ;clear per;
      unfold per_eq_bar in *; exrepnd.

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.
      pose proof (all_in_bar_type_sys_props4_implies_type_equality_respecting_trans ts lib bar bar0 A B A0 B0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp);[].

      exists B0 A b0 b3 a1 a2 eqa.
      dands; auto.

      {
        exists (intersect_bars bar bar0); dands; eauto 3 with slow.

        { eapply all_in_bar_type_sys_props4_implies_ts_sym;
            [apply implies_all_in_bar_intersect_bars_left;eauto|].
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans2;eauto. }

        { eapply implies_all_in_bar_eqorceq_sym;
            [|apply implies_all_in_bar_intersect_bars_left;eauto|]; eauto 3 with slow;[].
          eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto; eauto 3 with slow. }

        { eapply implies_all_in_bar_eqorceq_sym;
            [|apply implies_all_in_bar_intersect_bars_left;eauto|]; eauto 3 with slow;[].
          eapply implies_all_in_bar_eqorceq_trans_ccequivc; eauto; eauto 3 with slow. }
      }

      {
        eapply eq_term_equals_trans;[eauto|].
        eapply (eqorceq_implies_iff_per_eq_eq _ (intersect_bars bar bar0)); eauto 3 with slow.
        { apply eq_term_equals_sym; auto. }
        { eapply eq_term_equals_preserves_all_in_bar_term_equality_respecting; eauto 3 with slow. }
      }
    }

XXXX

    clear per;
    allunfold @per_eq; exrepd;
    ccomputes_to_eqval;
    unfold per_eq;
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum;
    try (assert (close lib ts A A0 eqa0)
                as k by (generalize (tygs A A0 eqa0); intro i; autodimp i h; rw <- i in c3; sp));
    try (assert (close lib ts B A0 eqa0)
                as k by (generalize (tygs B A0 eqa0); intro i; autodimp i h; rw <- i in c3; sp));
    try (assert (eq_term_equals eqa eqa0)
                as eqt by (apply uv with (T3 := A0); sp));
    try (assert (eq_term_equals eqa eqa0)
                as eqt by (apply uv with (T3 := B0); sp));
    apply eqorceq_eq_term_equals with (eq2 := eqa) in e0; auto;
    try (complete (apply eq_term_equals_sym; auto));
    apply eqorceq_eq_term_equals with (eq2 := eqa) in e; auto;
    try (complete (apply eq_term_equals_sym; auto)).

    (* 1 *)
    exists B0 A b0 b3 a1 a2 eqa0; sp; spcast; sp.

    generalize (tygs A B0 eqa0); intro i; autodimp i h; rw <- i; sp.

    apply eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply eqorceq_sym; auto.
    apply eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply eqorceq_sym; auto.

    rw t; repeat (rw <- eqt).
    split; sp.
    eapply eqorceq_commutes with (a := a1) (c := a2); eauto.
    eapply eqorceq_commutes with (a := b0) (c := b3); eauto.
    apply eqorceq_sym; auto.
    apply eqorceq_sym; auto.

    (* 2 *)
    exists A A0 a1 a2 a0 a3 eqa0; sp; spcast; sp.

    apply eqorceq_eq_term_equals with (eq2 := eqa); eauto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply eqorceq_sym; auto.
    apply eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply eqorceq_sym; auto.

    rw t; repeat (rw <- eqt).
    split; sp.
    eapply @eqorceq_commutes with (a := a0) (c := a3); eauto.
    eapply @eqorceq_commutes with (a := a1) (c := a2); eauto.
    apply eqorceq_sym; auto.
    apply eqorceq_sym; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_eq lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_eq lib (close lib ts) T' T4 eq2));

    clear per;
    allunfold @per_eq; exrepd;
    ccomputes_to_eqval;
    applydup @type_sys_props_ts_refl in IHX1; repnd;
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.

    (* 1 *)
    assert (close lib ts A A1 eqa1) as eqta1 by (generalize (tymt A A1 A eqa1 eqa); sp).
    assert (eq_term_equals eqa eqa1) as eqt1 by (apply uv with (T3 := A1); sp).
    assert (eq_term_equals eqa eqa0) as eqt2 by (apply uv with (T3 := B0); sp).
    assert (close lib ts A1 B0 eqa0) as eqta2 by (generalize (tymt A A1 B0 eqa1 eqa0); sp).

    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e2;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e1;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e0;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e;
    try (complete (apply eq_term_equals_sym; auto)).

    dands; apply CL_eq; unfold per_eq.

    exists A1 B0 a4 a5 b0 b3 eqa0; sp; spcast; sp.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply eqorceq_trans with (b := a1); auto.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_trans with (b := a2); auto.
    rw t0.
    allrw <-; sp.

    exists A1 B0 a4 a5 b0 b3 eqa0; sp; spcast; sp.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_trans with (b := a1); auto.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_trans with (b := a2); auto.
    rw t; repeat (rw <- eqt2); split; sp.
    eapply @eqorceq_commutes with (a := a1) (c := a2); eauto;
    try (complete (apply eqorceq_sym; auto)).
    eapply @eqorceq_commutes with (a := a4) (c := a5); eauto;
    try (complete (apply eqorceq_sym; auto)).

    (* 2 *)
    assert (close lib ts B A1 eqa1) as eqta1 by (generalize (tymt B A1 B eqa1 eqa); sp).
    assert (eq_term_equals eqa eqa1) as eqt1 by (apply uv with (T3 := A1); sp).
    assert (eq_term_equals eqa eqa0) as eqt2 by (apply uv with (T3 := B0); sp).
    assert (close lib ts A1 B0 eqa1) as cl by (generalize (tymt B A1 B0 eqa1 eqa0); intro i; autodimp i h; sp).

    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e2;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e1;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e0;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_eq_term_equals with (eq2 := eqa) in e;
    try (complete (apply eq_term_equals_sym; auto)).

    dands; apply CL_eq; unfold per_eq.

    exists A1 B0 a4 a5 b0 b3 eqa1; sp; spcast; sp.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_trans with (b := b1); auto.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_trans with (b := b2); auto.

    exists A1 B0 a4 a5 b0 b3 eqa1; sp; spcast; sp.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_trans with (b := b1); auto.
    apply @eqorceq_eq_term_equals with (eq2 := eqa); auto;
    try (complete (apply eq_term_equals_sym; auto)).
    apply @eqorceq_trans with (b := b2); auto.
    rw t; repeat (rw <- eqt1); repeat (rw <- eqt2); split; sp.
    eapply @eqorceq_commutes with (a := b1) (c := b2); eauto;
    try (complete (apply eqorceq_sym; auto)).
    eapply @eqorceq_commutes with (a := a4) (c := a5); eauto;
    try (complete (apply eqorceq_sym; auto)).
Qed.
