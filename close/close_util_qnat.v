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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.


Lemma per_qnat_bar_uniquely_valued {p} :
  forall inh (ts : cts(p)), uniquely_valued (per_qnat_bar inh ts).
Proof.
 unfold uniquely_valued, per_qnat_bar, eq_term_equals; sp.
 allrw; sp.
Qed.
Hint Resolve per_qnat_bar_uniquely_valued : slow.

Lemma per_qnat_bar_type_extensionality {p} :
  forall inh (ts : cts(p)), type_extensionality (per_qnat_bar inh ts).
Proof.
  unfold type_extensionality, per_qnat_bar, eq_term_equals; sp.
  allrw <-; sp.
Qed.
Hint Resolve per_qnat_bar_type_extensionality : slow.

Lemma per_qnat_bar_type_symmetric {p} :
  forall inh (ts : cts(p)), type_symmetric (per_qnat_bar inh ts).
Proof.
  unfold type_symmetric, per_qnat_bar; sp.
Qed.
Hint Resolve per_qnat_bar_type_symmetric : slow.

Lemma equality_of_qnat_sym {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_qnat lib t1 t2
    -> equality_of_qnat lib t2 t1.
Proof.
  introv e; unfold equality_of_qnat in *; exrepnd; spcast; dands; eexists; spcast; eauto.
Qed.
Hint Resolve equality_of_qnat_sym : slow.

Lemma per_qnat_bar_term_symmetric {p} :
  forall inh (ts : cts(p)), term_symmetric (per_qnat_bar inh ts).
Proof.
  introv h e.
  unfold per_qnat_bar in h; exrepnd.
  apply h in e; apply h.
  unfold equality_of_qnat_bar in *.
  eapply in_open_bar_pres; eauto; clear e; introv ext e.
  unfold equality_of_qnat in *; exrepnd.
  dands.
  { exists n; dands; eauto 3 with slow. }
  { exists n0; dands; eauto 3 with slow. }
Qed.
Hint Resolve per_qnat_bar_term_symmetric : slow.

Lemma cequivc_qnat {o} :
  forall lib (T T' : @CTerm o),
    computes_to_valc lib T mkc_qnat
    -> cequivc lib T T'
    -> computes_to_valc lib T' mkc_qnat.
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.
Hint Resolve cequivc_qnat : slow.

Lemma per_qnat_bar_type_value_respecting {p} :
  forall inh (ts : cts(p)), type_value_respecting inh (per_qnat_bar inh ts).
Proof.
  introv per ceq.
  unfold type_value_respecting, per_qnat_bar in *; exrepnd; GC.
  dands; auto;[].
  eapply in_open_bar_pres; eauto; clear per0; introv ext h; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_bar_type_value_respecting : slow.

Lemma per_qnat_bar_term_value_respecting {p} :
  forall inh (ts : cts(p)), term_value_respecting inh (per_qnat_bar inh ts).
Proof.
  introv h e ceq.
  unfold per_qnat_bar in *; exrepnd; spcast.
  apply h in e; apply h; clear h.
  unfold equality_of_qnat_bar in *.
  eapply in_open_bar_pres; eauto; clear e; introv ext e.
  unfold equality_of_qnat in *; exrepnd; GC; dands; eauto.
  pose proof (ceq _ ext) as ceq; simpl in *; spcast.
  exists n; spcast.
  apply cequivc_nat_implies_computes_to_valc.
  eapply cequivc_trans;[|eauto].
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; auto.
Qed.
Hint Resolve per_qnat_bar_term_value_respecting : slow.

Lemma per_qnat_bar_type_transitive {p} :
  forall inh (ts : cts(p)), type_transitive (per_qnat_bar inh ts).
Proof.
  introv per1 per2.
  unfold type_transitive, per_qnat_bar in *; exrepnd.
  dands; auto.
Qed.
Hint Resolve per_qnat_bar_type_transitive : slow.

Lemma ccequivc_ext_mkc_nat_implies {o} :
  forall inh (lib : @library o) k1 k2,
    ccequivc_ext inh lib (mkc_nat k1) (mkc_nat k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  apply cequivc_nat_implies_computes_to_valc in ceq.
  apply computes_to_valc_isvalue_eq in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma per_qnat_bar_term_transitive {p} :
  forall inh (ts : cts(p)), term_transitive (per_qnat_bar inh ts).
Proof.
  introv per i j.
  unfold per_qnat_bar in per; exrepnd.
  apply per in i; apply per in j; apply per.
  unfold equality_of_qnat_bar in *.
  exrepnd.

  clear per per0 per1.

  eapply in_open_bar_comb; try exact j; clear j.
  eapply in_open_bar_comb; try exact i; clear i.
  apply in_ext_implies_in_open_bar; introv ext i j.

  unfold equality_of_qnat in *; exrepnd.
  dands; eexists; eauto.
Qed.
Hint Resolve per_qnat_bar_term_transitive : slow.

Lemma per_qnat_type_system {p} :
  forall inh (ts : cts(p)), type_system inh (per_qnat_bar inh ts).
Proof.
  intros; unfold type_system; sp.
  - apply per_qnat_bar_uniquely_valued.
  - apply per_qnat_bar_type_extensionality.
  - apply per_qnat_bar_type_symmetric.
  - apply per_qnat_bar_type_transitive.
  - apply per_qnat_bar_type_value_respecting.
  - apply per_qnat_bar_term_symmetric.
  - apply per_qnat_bar_term_transitive.
  - apply per_qnat_bar_term_value_respecting.
Qed.
Hint Resolve per_qnat_type_system : slow.

Lemma ccequivc_ext_preserves_computes_to_valc_qnat {o} :
  forall inh lib (T T' : @CTerm o),
    ccequivc_ext inh lib T T'
    -> ccomputes_to_valc_ext inh lib T mkc_qnat
    -> T' ===>(inh,lib) mkc_qnat.
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma equality_of_qnat_bar_monotone {o} :
  forall {inh} {lib' lib : @library o} (ext : lib_extends inh lib' lib) t1 t2,
    equality_of_qnat_bar inh lib t1 t2
    -> equality_of_qnat_bar inh lib' t1 t2.
Proof.
  introv h; eapply sub_per_equality_of_qnat_bar; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_monotone : slow.

Lemma per_bar_eq_equality_of_qnat_bar_lib_per {o} :
  forall inh (lib : @library o),
    (per_bar_eq inh lib (equality_of_qnat_bar_lib_per inh lib))
    <=2=> (equality_of_qnat_bar inh lib).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.
  apply in_ext_ext_implies_in_open_bar_ext; introv; simpl; eauto 3 with slow.
Qed.

Lemma per_qnat_bar_implies_close {o} :
  forall inh (ts : cts(o)) lib T T' eq,
    per_qnat_bar inh (close inh ts) lib T T' eq
    -> close inh ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_qnat_bar in per; exrepnd.
  exists (equality_of_qnat_bar_lib_per inh lib).
  dands; eauto 3 with slow.

  - eapply in_open_bar_ext_comb2;try exact per0; clear per0.
    eapply in_open_bar_ext_comb2;try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext; introv pre1 per0.
    apply CL_qnat.
    unfold per_qnat; dands; auto.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_qnat_bar_lib_per.
Qed.

Lemma type_equality_respecting_trans1_per_qnat_bar_implies {o} :
  forall inh (ts : cts(o)) lib T T',
    type_system inh ts
    -> defines_only_universes inh ts
    -> type_monotone inh ts
    -> ccomputes_to_valc_ext inh lib T mkc_qnat
    -> ccomputes_to_valc_ext inh lib T' mkc_qnat
    -> type_equality_respecting_trans1 inh (per_qnat_bar inh (close inh ts)) lib T T'
    -> type_equality_respecting_trans1 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_qnat_bar_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - apply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; auto; spcast.
    dclose_lr; auto.
Qed.
Hint Resolve type_equality_respecting_trans1_per_qnat_bar_implies : slow.

Lemma type_equality_respecting_trans2_per_qnat_bar_implies {o} :
  forall inh (ts : cts(o)) lib T T',
    type_system inh ts
    -> defines_only_universes inh ts
    -> type_monotone inh ts
    -> ccomputes_to_valc_ext inh lib T mkc_qnat
    -> ccomputes_to_valc_ext inh lib T' mkc_qnat
    -> type_equality_respecting_trans2 inh (per_qnat_bar inh (close inh ts)) lib T T'
    -> type_equality_respecting_trans2 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_qnat_bar_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.
Hint Resolve type_equality_respecting_trans2_per_qnat_bar_implies : slow.
