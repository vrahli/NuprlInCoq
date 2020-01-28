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


(*
Lemma per_csname_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_bar (per_csname ts)).
Proof.
 unfold uniquely_valued, per_csname_bar, eq_term_equals; sp.
 allrw; sp.
Qed.
Hint Resolve per_csname_bar_uniquely_valued : slow.

Lemma per_csname_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_csname_bar ts).
Proof.
  unfold type_extensionality, per_csname_bar, eq_term_equals; sp.
  allrw <-; sp.
Qed.
Hint Resolve per_csname_bar_type_extensionality : slow.

Lemma per_csname_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_csname_bar ts).
Proof.
  introv per.
  unfold per_csname_bar in *; exrepnd; dands; auto.
  exists bar; dands; auto.
Qed.
Hint Resolve per_csname_bar_type_symmetric : slow.

Lemma per_csname_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_csname_bar ts).
Proof.
  introv per1 per2.
  unfold per_csname_bar in *; exrepnd; dands; auto.

  exists (intersect_bars bar bar0).
  dands.

  - introv i j; simpl in *; exrepnd.
    pose proof (per3 lib2) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per4 lib1) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.
Qed.
Hint Resolve per_csname_bar_type_transitive : slow.
*)

Lemma cequiv_csname {pp} :
  forall lib T T' n,
    @computes_to_value pp lib T (mk_csname n)
    -> cequiv lib T T'
    -> computes_to_value lib T' (mk_csname n).
Proof.
  sp.
  apply cequiv_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv0 in p; subst; auto.
Qed.

Lemma cequivc_csname {pp} :
  forall lib T T' n,
    computes_to_valc lib T (mkc_csname n)
    -> @cequivc pp lib T T'
    -> computes_to_valc lib T' (mkc_csname n).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

(*Lemma per_csname_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_csname_bar ts).
Proof.
  introv per ceq.
  unfold type_value_respecting, per_csname_bar in *; exrepnd.
  dands; auto;[].
  exists bar; dands; auto.
  introv ie i.
  applydup per0 in i; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  eapply cequivc_csname; eauto.
Qed.
Hint Resolve per_csname_bar_type_value_respecting : slow.

Lemma per_csname_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_csname_bar ts).
Proof.
  introv; unfold term_symmetric, term_equality_symmetric, per_csname_bar.
  introv k e; repnd.
  allrw.
  apply k in e.
  allunfold @equality_of_csname_bar; exrepnd.
  exists bar.
  introv ie i.
  apply e0 in i; eauto 3 with slow.
  unfold equality_of_csname in *.
  exrepnd; exists name; tcsp.
Qed.
Hint Resolve per_csname_bar_term_symmetric : slow.

Lemma per_csname_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_csname_bar ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_csname_bar.
  introv cts per i j.
  exrepnd.
  rw per in i; rw per in j; rw per; clear per.
  allunfold @equality_of_csname_bar; exrepnd.

  exists (intersect_bars bar1 bar0).
  unfold equality_of_csname in *.
  introv i j; simpl in *; exrepnd.

  pose proof (i0 lib1) as q; autodimp q hyp; clear i0.
  pose proof (q lib'0) as w; clear q; autodimp w hyp; eauto 2 with slow; simpl in w.

  pose proof (j0 lib2) as q; autodimp q hyp; clear j0.
  pose proof (q lib'0) as z; clear q; autodimp z hyp; eauto 2 with slow; simpl in z.
  exrepnd; spcast.
  computes_to_eqval.
  eexists; dands; spcast; eauto.
Qed.
Hint Resolve per_csname_bar_term_transitive : slow.
*)

Lemma cequivc_choice_seq {pp} :
  forall lib T T' u,
    computes_to_valc lib T (mkc_choice_seq u)
    -> @cequivc pp lib T T'
    -> computes_to_valc lib T' (mkc_choice_seq u).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

(*Lemma per_csname_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_csname_bar ts).
Proof.
  introv h e ceq.
  unfold per_nat_bar in *; exrepnd; spcast.
  apply h in e; apply h; clear h.
  unfold equality_of_csname_bar in *.
  exrepnd; exists bar.
  introv ie i; applydup e0 in i; auto.
  unfold equality_of_csname in *; exrepnd.
  exists name; repnd; dands; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  eapply cequivc_choice_seq; eauto.
Qed.
Hint Resolve per_csname_bar_term_value_respecting : slow.

Lemma per_csname_bar_type_system {p} :
  forall (ts : cts(p)), type_system (per_csname_bar ts).
Proof.
  intros; unfold type_system; sp.
  - apply per_csname_bar_uniquely_valued; auto.
  - apply per_csname_bar_type_extensionality; auto.
  - apply per_csname_bar_type_symmetric; auto.
  - apply per_csname_bar_type_transitive; auto.
  - apply per_csname_bar_type_value_respecting; auto.
  - apply per_csname_bar_term_symmetric; auto.
  - apply per_csname_bar_term_transitive; auto.
  - apply per_csname_bar_term_value_respecting; auto.
Qed.
Hint Resolve per_csname_bar_type_system : slow.
*)

Lemma ccequivc_ext_preserves_computes_to_valc_csname {o} :
  forall lib (T T' : @CTerm o) n,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_csname n)
    -> T' ===>(lib) (mkc_csname n).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma equality_of_csname_bar_monotone {o} :
  forall {lib' lib : @library o} (ext : lib_extends lib' lib) n t1 t2,
    equality_of_csname_bar lib n t1 t2
    -> equality_of_csname_bar lib' n t1 t2.
Proof.
  introv ext h.
  eapply sub_per_equality_of_csname_bar; eauto 3 with slow.
Qed.
Hint Resolve equality_of_csname_bar_monotone : slow.

Lemma per_bar_eq_equality_of_csname_bar_lib_per {o} :
  forall (lib : @library o) n,
    (per_bar_eq lib (equality_of_csname_bar_lib_per lib n))
    <=2=> (equality_of_csname_bar lib n).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.
  apply in_ext_ext_implies_in_open_bar_ext; introv; simpl; eauto 3 with slow.
Qed.

(*Lemma per_csname_bar_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_csname_bar (close ts) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_csname_bar in per; exrepnd.
  exists bar (equality_of_csname_bar_lib_per lib).
  dands; eauto 3 with slow.

  - introv br ext; introv; simpl.
    pose proof (per0 _ br _ ext) as per0; simpl in *.
    pose proof (per1 _ br _ ext) as per1; simpl in *.
    apply CL_csname.
    unfold per_csname; dands; auto.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_csname_bar_lib_per.
Qed.

Lemma type_equality_respecting_trans_per_csname_bar_implies {o} :
  forall (ts : cts(o)) lib T T',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T mkc_csname
    -> computes_to_valc lib T' mkc_csname
    -> type_equality_respecting_trans (per_csname_bar (close ts)) lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_csname_bar_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - apply ccequivc_ext_preserves_computes_to_valc_csname in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_csname in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_csname in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_csname in ceq; auto; spcast.
    dclose_lr; auto.
Qed.
 *)



Lemma per_bar_per_csname_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_csname (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb;try exact per1; clear per1.
  apply in_ext_ext_implies_in_open_bar_ext; introv pre1.
  apply CL_csname; auto.
Qed.

Lemma ccequivc_ext_csname {o} :
  forall lib (T T' : @CTerm o) n,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_csname n)
    -> ccomputes_to_valc lib T' (mkc_csname n).
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_csname in ceq';[|eauto]; exrepnd; auto.
Qed.

Lemma type_equality_respecting_trans1_per_csname_bar_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_csname n)
    -> ccomputes_to_valc_ext lib T' (mkc_csname n')
    -> type_equality_respecting_trans1 (per_bar (per_csname (close ts))) lib T T'
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_bar_per_csname_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_per_csname_bar_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_csname n)
    -> ccomputes_to_valc_ext lib T' (mkc_csname n')
    -> type_equality_respecting_trans2 (per_bar (per_csname (close ts))) lib T T'
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_bar_per_csname_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.

Lemma per_bar_eq_per_csname_eq_bar_lib_per {o} :
  forall (lib : @library o) n,
    (per_bar_eq lib (equality_of_csname_bar_lib_per lib n))
    <=2=> (equality_of_csname_bar lib n).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.
  apply in_ext_ext_implies_in_open_bar_ext; introv; simpl; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_mkc_csname_implies {o} :
  forall (lib : @library o) k1 k2,
    ccequivc_ext lib (mkc_csname k1) (mkc_csname k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  eapply cequivc_csname in ceq;[|eauto 3 with slow].
  apply computes_to_valc_isvalue_eq in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma per_csname_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_csname ts).
Proof.
  unfold uniquely_valued, per_csname, eq_term_equals; sp.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_csname_implies in ceq; subst.
  spcast; allrw; sp.
Qed.
Hint Resolve per_csname_uniquely_valued : slow.

Lemma per_bar_per_csname_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_csname_uniquely_valued : slow.

Lemma per_csname_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_csname ts).
Proof.
  introv per eqiff.
  unfold per_csname in *; exrepnd.
  exists n; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve per_csname_type_extensionality : slow.

Lemma per_bar_per_csname_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_csname_type_extensionality : slow.

Lemma per_csname_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_csname ts).
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists n; dands; auto.
Qed.
Hint Resolve per_csname_type_symmetric : slow.

Lemma per_bar_per_csname_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_csname_type_symmetric : slow.

Lemma per_csname_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_csname ts).
Proof.
  introv pera perb.
  unfold per_csname in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_csname_implies in ceq; subst; GC.
  exists n0; dands; spcast; auto.
Qed.
Hint Resolve per_csname_type_transitive : slow.

Lemma per_bar_per_csname_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_csname_type_transitive : slow.

Lemma per_csname_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_csname ts).
Proof.
  introv per ceq.
  unfold per_csname in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_csname_implies in ceq0; subst; GC.
  exists n; dands; spcast; auto; eauto 3 with slow.
Qed.
Hint Resolve per_csname_type_value_respecting : slow.

Lemma per_bar_per_csname_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_csname_type_value_respecting : slow.

Lemma type_equality_respecting_trans1_per_bar_per_csname_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T  (mkc_csname n)
    -> ccomputes_to_valc_ext lib T' (mkc_csname n')
    -> type_equality_respecting_trans1 (per_bar (per_csname (close ts))) lib T T'
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou mon comp1 comp2 trans h ceq cl.
  apply per_bar_per_csname_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq; eauto 3 with slow.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq; eauto 3 with slow.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq; eauto 3 with slow.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_csname in ceq; eauto 3 with slow.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_per_bar_per_csname_implies {o} :
  forall (ts : cts(o)) lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T  (mkc_csname n)
    -> ccomputes_to_valc_ext lib T' (mkc_csname n')
    -> type_equality_respecting_trans2 (per_bar (per_csname (close ts))) lib T T'
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou mon comp1 comp2 trans h ceq cl.
  apply per_bar_per_csname_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.

Lemma per_csname_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_csname ts).
Proof.
  introv pera perb.
  unfold per_csname in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw pera0; clear pera0.

  unfold equality_of_csname_bar in *; exrepnd.
  eapply in_open_bar_pres; eauto; clear perb; introv ext perb.
  unfold equality_of_csname in *; exrepnd; exists name; dands; eauto 3 with slow.
Qed.
Hint Resolve per_csname_term_symmetric : slow.

Lemma per_bar_per_csname_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_csname_term_symmetric : slow.

Lemma iscvalue_mkc_choice_seq {o} :
  forall i, @iscvalue o (mkc_choice_seq i).
Proof.
  introv; unfold iscvalue; simpl; eauto with slow.
Qed.
Hint Resolve iscvalue_mkc_choice_seq : slow.

Lemma ccequivc_ext_mkc_choice_seq_implies {o} :
  forall (lib : @library o) k1 k2,
    ccequivc_ext lib (mkc_choice_seq k1) (mkc_choice_seq k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  eapply cequivc_choice_seq in ceq;[|eauto 3 with slow].
  apply computes_to_valc_isvalue_eq in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma per_csname_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_csname ts).
Proof.
  introv per e1 e2.
  unfold per_csname in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw per0; clear per0.

  unfold equality_of_csname_bar in *; exrepnd.

  eapply in_open_bar_comb; try exact e1; clear e1.
  eapply in_open_bar_comb; try exact e2; clear e2.
  apply in_ext_implies_in_open_bar; introv ext i j.

  unfold equality_of_csname in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_choice_seq_implies in ceq; subst; GC.

  exists name0; dands; spcast; auto.
Qed.
Hint Resolve per_csname_term_transitive : slow.

Lemma per_bar_per_csname_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_csname_term_transitive : slow.

Lemma per_csname_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_csname ts).
Proof.
  introv per e ceq.
  unfold per_csname in *; exrepnd.
  allrw per0; clear per0.

  unfold equality_of_csname_bar in *; exrepnd.
  eapply in_open_bar_pres; eauto; clear e; introv ext e.
  unfold equality_of_csname in *; exrepnd; dands; auto.
  exists name; dands; spcast; auto; eauto 3 with slow.
Qed.
Hint Resolve per_csname_term_value_respecting : slow.

Lemma per_bar_per_csname_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_bar (per_csname ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_csname_term_value_respecting : slow.

Lemma per_bar_per_csname_type_system {p} :
  forall (ts : cts(p)), type_system (per_bar (per_csname ts)).
Proof.
  intros; unfold type_system; sp; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_csname_type_system : slow.

Lemma per_bar_per_csname_uniquely_valued2 {p} :
  forall (ts : cts(p)), uniquely_valued2 (per_bar (per_csname ts)).
Proof.
  unfold uniquely_valued2; introv pera perb; allunfold @per_bar; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  clear dependent eq.
  clear dependent eq'.

  apply implies_eq_term_equals_per_bar_eq.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.
  unfold per_csname in *; exrepnd; spcast.

  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_csname_implies in ceq; subst; GC.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  introv; tcsp.
Qed.
Hint Resolve per_bar_per_csname_uniquely_valued2 : slow.

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
