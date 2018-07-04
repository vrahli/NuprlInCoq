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
  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.
Require Export close_util_bar.
Require Export close_util1.


Lemma cequiv_refname {pp} :
  forall lib T T' n,
    @computes_to_value pp lib T (mk_refname n)
    -> cequiv lib T T'
    -> computes_to_value lib T' (mk_refname n).
Proof.
  sp.
  apply cequiv_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv0 in p; subst; auto.
Qed.

Lemma cequivc_refname {pp} :
  forall lib T T' n,
    computes_to_valc lib T (mkc_refname n)
    -> @cequivc pp lib T T'
    -> computes_to_valc lib T' (mkc_refname n).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

(*Lemma per_refname_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_refname_bar ts).
Proof.
  introv per ceq.
  unfold type_value_respecting, per_refname_bar in *; exrepnd.
  dands; auto;[].
  exists bar; dands; auto.
  introv ie i.
  applydup per0 in i; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  eapply cequivc_refname; eauto.
Qed.
Hint Resolve per_refname_bar_type_value_respecting : slow.

Lemma per_refname_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_refname_bar ts).
Proof.
  introv; unfold term_symmetric, term_equality_symmetric, per_refname_bar.
  introv k e; repnd.
  allrw.
  apply k in e.
  allunfold @equality_of_refname_bar; exrepnd.
  exists bar.
  introv ie i.
  apply e0 in i; eauto 3 with slow.
  unfold equality_of_refname in *.
  exrepnd; exists name; tcsp.
Qed.
Hint Resolve per_refname_bar_term_symmetric : slow.

Lemma per_refname_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_refname_bar ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_refname_bar.
  introv cts per i j.
  exrepnd.
  rw per in i; rw per in j; rw per; clear per.
  allunfold @equality_of_refname_bar; exrepnd.

  exists (intersect_bars bar1 bar0).
  unfold equality_of_refname in *.
  introv i j; simpl in *; exrepnd.

  pose proof (i0 lib1) as q; autodimp q hyp; clear i0.
  pose proof (q lib'0) as w; clear q; autodimp w hyp; eauto 2 with slow; simpl in w.

  pose proof (j0 lib2) as q; autodimp q hyp; clear j0.
  pose proof (q lib'0) as z; clear q; autodimp z hyp; eauto 2 with slow; simpl in z.
  exrepnd; spcast.
  computes_to_eqval.
  eexists; dands; spcast; eauto.
Qed.
Hint Resolve per_refname_bar_term_transitive : slow.
*)

Lemma cequivc_ref {pp} :
  forall lib T T' u,
    computes_to_valc lib T (mkc_ref u)
    -> @cequivc pp lib T T'
    -> computes_to_valc lib T' (mkc_ref u).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

(*Lemma per_refname_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_refname_bar ts).
Proof.
  introv h e ceq.
  unfold per_nat_bar in *; exrepnd; spcast.
  apply h in e; apply h; clear h.
  unfold equality_of_refname_bar in *.
  exrepnd; exists bar.
  introv ie i; applydup e0 in i; auto.
  unfold equality_of_refname in *; exrepnd.
  exists name; repnd; dands; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  eapply cequivc_choice_seq; eauto.
Qed.
Hint Resolve per_refname_bar_term_value_respecting : slow.

Lemma per_refname_bar_type_system {p} :
  forall (ts : cts(p)), type_system (per_refname_bar ts).
Proof.
  intros; unfold type_system; sp.
  - apply per_refname_bar_uniquely_valued; auto.
  - apply per_refname_bar_type_extensionality; auto.
  - apply per_refname_bar_type_symmetric; auto.
  - apply per_refname_bar_type_transitive; auto.
  - apply per_refname_bar_type_value_respecting; auto.
  - apply per_refname_bar_term_symmetric; auto.
  - apply per_refname_bar_term_transitive; auto.
  - apply per_refname_bar_term_value_respecting; auto.
Qed.
Hint Resolve per_refname_bar_type_system : slow.
*)

Lemma ccequivc_ext_preserves_computes_to_valc_refname {o} :
  forall lib (T T' : @CTerm o) n,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_refname n)
    -> T' ===>(lib) (mkc_refname n).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma equality_of_refname_bar_monotone {o} :
  forall {lib' lib : @SL o} (ext : lib_extends lib' lib) n t1 t2,
    equality_of_refname_bar lib n t1 t2
    -> equality_of_refname_bar lib' n t1 t2.
Proof.
  introv ext h.
  eapply sub_per_equality_of_refname_bar; eauto 3 with slow.
Qed.
Hint Resolve equality_of_refname_bar_monotone : slow.

Lemma per_bar_eq_equality_of_refname_bar_lib_per {o} :
  forall (lib : SL) (bar : @BarLib o lib) n,
    (per_bar_eq bar (equality_of_refname_bar_lib_per lib n))
    <=2=> (equality_of_refname_bar lib n).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.
  introv br ext; introv; simpl.
  exists (trivial_bar lib'0).
  apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
  introv y; eauto 3 with slow.
Qed.

(*Lemma per_refname_bar_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_refname_bar (close ts) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_refname_bar in per; exrepnd.
  exists bar (equality_of_refname_bar_lib_per lib).
  dands; eauto 3 with slow.

  - introv br ext; introv; simpl.
    pose proof (per0 _ br _ ext) as per0; simpl in *.
    pose proof (per1 _ br _ ext) as per1; simpl in *.
    apply CL_refname.
    unfold per_refname; dands; auto.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_refname_bar_lib_per.
Qed.

Lemma type_equality_respecting_trans_per_refname_bar_implies {o} :
  forall (ts : cts(o)) lib T T',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T mkc_refname
    -> computes_to_valc lib T' mkc_refname
    -> type_equality_respecting_trans (per_refname_bar (close ts)) lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_refname_bar_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - apply ccequivc_ext_preserves_computes_to_valc_refname in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_refname in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_refname in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_refname in ceq; auto; spcast.
    dclose_lr; auto.
Qed.
 *)



Lemma per_bar_per_refname_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_refname (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply CL_refname; auto.
Qed.

Lemma ccequivc_ext_refname {o} :
  forall lib (T T' : @CTerm o) n,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_refname n)
    -> ccomputes_to_valc lib T' (mkc_refname n).
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_refname in ceq';[|eauto]; exrepnd; auto.
Qed.

Lemma type_equality_respecting_trans1_per_refname_bar_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_refname n)
    -> ccomputes_to_valc_ext lib T' (mkc_refname n')
    -> type_equality_respecting_trans1 (per_bar (per_refname (close ts))) lib T T'
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_bar_per_refname_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_per_refname_bar_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_refname n)
    -> ccomputes_to_valc_ext lib T' (mkc_refname n')
    -> type_equality_respecting_trans2 (per_bar (per_refname (close ts))) lib T T'
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_bar_per_refname_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.

Lemma per_bar_eq_per_refname_eq_bar_lib_per {o} :
  forall (lib : SL) (bar : @BarLib o lib) n,
    (per_bar_eq bar (equality_of_refname_bar_lib_per lib n))
    <=2=> (equality_of_refname_bar lib n).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  unfold equality_of_refname_bar in h; exrepnd.
  introv br ext; introv.
  exists (raise_bar bar0 x); introv br' ext'; introv; simpl in *; exrepnd.
  exists (trivial_bar lib'2).
  apply in_ext_implies_all_in_bar_trivial_bar; introv y.
  apply (h0 _ br'1 lib'3); eauto 3 with slow.
Qed.

Lemma ccequivc_ext_mkc_refname_implies {o} :
  forall (lib : @SL o) k1 k2,
    ccequivc_ext lib (mkc_refname k1) (mkc_refname k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  eapply cequivc_refname in ceq;[|eauto 3 with slow].
  apply computes_to_valc_isvalue_eq in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma per_refname_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_refname ts).
Proof.
  unfold uniquely_valued, per_refname, eq_term_equals; sp.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_refname_implies in ceq; subst.
  spcast; allrw; sp.
Qed.
Hint Resolve per_refname_uniquely_valued : slow.

Lemma per_bar_per_refname_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_refname_uniquely_valued : slow.

Lemma per_refname_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_refname ts).
Proof.
  introv per eqiff.
  unfold per_refname in *; exrepnd.
  exists n; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve per_refname_type_extensionality : slow.

Lemma per_bar_per_refname_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_refname_type_extensionality : slow.

Lemma per_refname_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_refname ts).
Proof.
  introv per.
  unfold per_refname in *; exrepnd.
  exists n; dands; auto.
Qed.
Hint Resolve per_refname_type_symmetric : slow.

Lemma per_bar_per_refname_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_refname_type_symmetric : slow.

Lemma per_refname_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_refname ts).
Proof.
  introv pera perb.
  unfold per_refname in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_refname_implies in ceq; subst; GC.
  exists n0; dands; spcast; auto.
Qed.
Hint Resolve per_refname_type_transitive : slow.

Lemma per_bar_per_refname_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_refname_type_transitive : slow.

Lemma per_refname_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_refname ts).
Proof.
  introv per ceq.
  unfold per_refname in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_refname_implies in ceq0; subst; GC.
  exists n; dands; spcast; auto; eauto 3 with slow.
Qed.
Hint Resolve per_refname_type_value_respecting : slow.

Lemma per_bar_per_refname_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_refname_type_value_respecting : slow.

Lemma type_equality_respecting_trans1_per_bar_per_refname_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T  (mkc_refname n)
    -> ccomputes_to_valc_ext lib T' (mkc_refname n')
    -> type_equality_respecting_trans1 (per_bar (per_refname (close ts))) lib T T'
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou mon comp1 comp2 trans h ceq cl.
  apply per_bar_per_refname_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq; eauto 3 with slow.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq; eauto 3 with slow.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq; eauto 3 with slow.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_refname in ceq; eauto 3 with slow.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_per_bar_per_refname_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T  (mkc_refname n)
    -> ccomputes_to_valc_ext lib T' (mkc_refname n')
    -> type_equality_respecting_trans2 (per_bar (per_refname (close ts))) lib T T'
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou mon comp1 comp2 trans h ceq cl.
  apply per_bar_per_refname_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.

Lemma per_refname_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_refname ts).
Proof.
  introv pera perb.
  unfold per_refname in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw pera0; clear pera0.

  unfold equality_of_refname_bar in *; exrepnd.
  exists bar; introv br ext; introv.
  pose proof (perb0 _ br _ ext) as perb0; simpl in *.

  unfold equality_of_refname in *; exrepnd; exists name; dands; auto.
Qed.
Hint Resolve per_refname_term_symmetric : slow.

Lemma per_bar_per_refname_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_refname_term_symmetric : slow.

Lemma isvalue_mk_ref {o} :
  forall i, @isvalue o (mk_ref i).
Proof.
  introv; repeat constructor; simpl; tcsp.
Qed.
Hint Resolve isvalue_mk_ref : slow.

Lemma iscvalue_mkc_ref {o} :
  forall i, @iscvalue o (mkc_ref i).
Proof.
  introv; unfold iscvalue; simpl; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_mkc_ref  : slow.

Lemma ccequivc_ext_mkc_ref_implies {o} :
  forall (lib : @SL o) k1 k2,
    ccequivc_ext lib (mkc_ref k1) (mkc_ref k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  eapply cequivc_ref in ceq;[|eauto 3 with slow].
  apply computes_to_valc_isvalue_eq in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma per_refname_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_refname ts).
Proof.
  introv per e1 e2.
  unfold per_refname in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw per0; clear per0.

  unfold equality_of_refname_bar in *; exrepnd.
  exists (intersect_bars bar bar0); introv br ext; introv; simpl in *; exrepnd.
  pose proof (e1 _ br2 lib'0 (lib_extends_trans ext br1)) as e1; simpl in *.
  pose proof (e0 _ br0 lib'0 (lib_extends_trans ext br3)) as e0; simpl in *.

  unfold equality_of_refname in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_ref_implies in ceq; subst; GC.

  exists name0; dands; spcast; auto.
Qed.
Hint Resolve per_refname_term_transitive : slow.

Lemma per_bar_per_refname_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_refname_term_transitive : slow.

Lemma per_refname_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_refname ts).
Proof.
  introv per e ceq.
  unfold per_refname in *; exrepnd.
  allrw per0; clear per0.

  unfold equality_of_refname_bar in *; exrepnd.
  exists bar; introv br ext; introv; simpl in *; exrepnd.
  pose proof (e0 _ br _ ext) as e0; simpl in *.
  unfold equality_of_refname in *; exrepnd; dands; auto.
  assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
  exists name; dands; spcast; auto; eauto 3 with slow.
Qed.
Hint Resolve per_refname_term_value_respecting : slow.

Lemma per_bar_per_refname_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_bar (per_refname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_refname_term_value_respecting : slow.

Lemma per_bar_per_refname_type_system {p} :
  forall (ts : cts(p)), type_system (per_bar (per_refname ts)).
Proof.
  intros; unfold type_system; sp; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_refname_type_system : slow.

Lemma per_bar_per_refname_uniquely_valued2 {p} :
  forall (ts : cts(p)), uniquely_valued2 (per_bar (per_refname ts)).
Proof.
  unfold uniquely_valued2; introv pera perb; allunfold @per_bar; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  clear dependent eq.
  clear dependent eq'.

  eapply eq_term_equals_trans;
    [apply eq_term_equals_sym;
     eapply (per_bar_eq_intersect_bars_left _ bar)|].
  eapply eq_term_equals_trans;
    [|eapply (per_bar_eq_intersect_bars_right _ bar0)].

  apply (implies_all_in_bar_ext_intersect_bars_left _ bar) in pera0.
  apply (implies_all_in_bar_ext_intersect_bars_right _ bar0) in perb0.

  remember (intersect_bars bar0 bar) as b.
  clear dependent bar0.
  clear dependent bar.
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same.

  introv br ext; introv.
  pose proof (pera0 _ br _ ext x) as pera0.
  pose proof (perb0 _ br _ ext x) as perb0.
  simpl in *.
  unfold per_refname in *; exrepnd; spcast.

  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_refname_implies in ceq; subst; GC.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  introv; tcsp.
Qed.
Hint Resolve per_bar_per_refname_uniquely_valued2 : slow.

(*Lemma per_cequiv_uniquely_valued2 {p} :
  forall (ts : cts(p)), uniquely_valued2 (per_cequiv ts).
Proof.
  unfold uniquely_valued2, per_cequiv, eq_term_equals; sp.
  spcast; repeat computes_to_eqval.
  allrw; sp.
Qed.
Hint Resolve per_cequiv_uniquely_valued2 : slow.

Lemma per_bar_per_cequiv_uniquely_valued2 {p} :
  forall (ts : cts(p)), uniquely_valued2 (per_bar (per_cequiv ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_cequiv_uniquely_valued2 : slow.
 *)
