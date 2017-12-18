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


  Website: http://nuprl.org/html/verification/
  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.


Lemma per_csname_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_csname_bar ts).
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

Lemma cequiv_csname {pp} :
  forall lib T T',
    @computes_to_value pp lib T mk_csname
    -> cequiv lib T T'
    -> computes_to_value lib T' mk_csname.
Proof.
  sp.
  apply cequiv_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv0 in p; subst; auto.
Qed.

Lemma cequivc_csname {pp} :
  forall lib T T',
    computes_to_valc lib T mkc_csname
    -> @cequivc pp lib T T'
    -> computes_to_valc lib T' mkc_csname.
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

Lemma per_csname_bar_type_value_respecting {p} :
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

Lemma per_csname_bar_term_value_respecting {p} :
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

Lemma ccequivc_ext_preserves_computes_to_valc_csname {o} :
  forall lib (T T' : @CTerm o),
    ccequivc_ext lib T T'
    -> computes_to_valc lib T mkc_csname
    -> T' ===>(lib) mkc_csname.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *.
  spcast; eapply cequivc_csname; eauto.
Qed.

Lemma equality_of_csname_bar_monotone {o} :
  forall {lib' lib : @library o} (ext : lib_extends lib' lib) t1 t2,
    equality_of_csname_bar lib t1 t2
    -> equality_of_csname_bar lib' t1 t2.
Proof.
  introv h; eapply sub_per_equality_of_csname_bar; eauto 3 with slow.
Qed.
Hint Resolve equality_of_csname_bar_monotone : slow.

Lemma per_bar_eq_equality_of_csname_bar_lib_per {o} :
  forall lib (bar : @BarLib o lib),
    (per_bar_eq bar (equality_of_csname_bar_lib_per lib))
    <=2=> (equality_of_csname_bar lib).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.
  introv br ext; introv; simpl.
  exists (trivial_bar lib'0).
  apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
  introv y; eauto 3 with slow.
Qed.

Lemma per_csname_bar_implies_close {o} :
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
