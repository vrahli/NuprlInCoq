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
Require Export close_util1.


Lemma in_open_bar_mkc_qnat_implies_same_cond {o} :
  forall (lib : @library o) T c1 c2,
    in_open_bar lib (fun lib : library => (T) ===>(lib) (mkc_qnat c1))
    -> in_open_bar lib (fun lib : library => (T) ===>(lib) (mkc_qnat c2))
    -> c1 = c2.
Proof.
  introv h q.
  apply (in_open_bar_const lib).
  eapply in_open_bar_comb; try exact h; clear h.
  eapply in_open_bar_pres; try exact q; clear q.
  introv ext h q.
  computes_to_eqval.
  apply cequivc_qnat_left_iscvalue in eqt; eauto 3 with slow.
  apply mkc_qnat_eq in eqt; auto.
Qed.

Lemma per_qnat_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_qnat_bar ts).
Proof.
 unfold uniquely_valued, per_qnat_bar, eq_term_equals; sp.
 assert (c0 = c) by (eapply in_open_bar_mkc_qnat_implies_same_cond; eauto); subst.
 allrw; sp.
Qed.
Hint Resolve per_qnat_bar_uniquely_valued : slow.

Lemma ccequivc_ext_mkc_qnat_implies {o} :
  forall (lib : @library o) k1 k2,
    ccequivc_ext lib (mkc_qnat k1) (mkc_qnat k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  apply cequivc_qnat_left_iscvalue in ceq; eauto 3 with slow.
  apply mkc_qnat_eq in ceq; auto.
Qed.

Lemma ccequivc_ext_mkc_nat_implies {o} :
  forall (lib : @library o) k1 k2,
    ccequivc_ext lib (mkc_nat k1) (mkc_nat k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  apply cequivc_nat_implies_computes_to_valc in ceq.
  apply computes_to_valc_isvalue_eq in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma per_qnat_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_qnat ts).
Proof.
  unfold uniquely_valued, per_qnat, eq_term_equals; sp.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_qnat_implies in ceq; subst.
  spcast; allrw; sp.
Qed.
Hint Resolve per_qnat_uniquely_valued : slow.

Lemma per_bar_per_qnat_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_qnat_uniquely_valued : slow.

Lemma per_qnat_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_qnat ts).
Proof.
  introv per eqiff.
  unfold per_qnat in *; exrepnd.
  eexists; dands; eauto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve per_qnat_type_extensionality : slow.

Lemma per_bar_per_qnat_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_qnat_type_extensionality : slow.

Lemma per_qnat_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_qnat_bar ts).
Proof.
  unfold type_extensionality, per_qnat_bar, eq_term_equals; sp.
  eexists; dands; eauto; introv; allrw <-; sp.
Qed.
Hint Resolve per_qnat_bar_type_extensionality : slow.

Lemma per_qnat_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_qnat ts).
Proof.
  introv per.
  unfold per_qnat in *; exrepnd.
  eexists; dands; eauto.
Qed.
Hint Resolve per_qnat_type_symmetric : slow.

Lemma per_bar_per_qnat_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_type_symmetric : slow.

Lemma per_qnat_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_qnat_bar ts).
Proof.
  unfold type_symmetric, per_qnat_bar; sp; eexists; dands; eauto.
Qed.
Hint Resolve per_qnat_bar_type_symmetric : slow.

Lemma sat_qnat_cond_sym {o} :
  forall (lib : @library o) c t1 t2,
    in_ext lib (fun lib => exists n, ccomputes_to_valc lib t1 (mkc_nat n) # ccomputes_to_valc lib t2 (mkc_nat n))
    -> sat_qnat_cond lib c t1
    -> sat_qnat_cond lib c t2.
Proof.
  introv h sat q exta extb compa compb; subst.
  pose proof (h _ exta) as ha; simpl in ha; exrepnd.
  pose proof (h _ (lib_extends_trans extb exta)) as hb; simpl in hb; exrepnd.
  repeat ccomputes_to_eqval.
  eapply sat; eauto.
Qed.
Hint Resolve sat_qnat_cond_sym : slow.

Lemma are_same_qnats_sym {o} :
  forall lib c (t1 t2 : @CTerm o),
    are_same_qnats lib c t1 t2
    -> are_same_qnats lib c t2 t1.
Proof.
  introv h ext; apply h in ext; clear h;
    exrepnd; spcast; dands; eexists; spcast; dands; spcast; eauto.
Qed.
Hint Resolve are_same_qnats_sym : slow.

Lemma equality_of_qnat_sym {o} :
  forall lib c (t1 t2 : @CTerm o),
    equality_of_qnat lib c t1 t2
    -> equality_of_qnat lib c t2 t1.
Proof.
  introv e; unfold equality_of_qnat in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_sym : slow.

Lemma equality_of_qnat_bar_sym {o} :
  forall (lib : @library o) c t1 t2,
    equality_of_qnat_bar lib c t1 t2
    -> equality_of_qnat_bar lib c t2 t1.
Proof.
  introv equ.
  eapply in_open_bar_pres; eauto; clear equ; introv ext equ; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_sym : slow.

Lemma per_qnat_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_qnat_bar ts).
Proof.
  introv h e.
  unfold per_qnat_bar in h; exrepnd.
  apply h0 in e; apply h0; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_bar_term_symmetric : slow.

Lemma cequivc_qnat {o} :
  forall lib c (T T' : @CTerm o),
    computes_to_valc lib T (mkc_qnat c)
    -> cequivc lib T T'
    -> computes_to_valc lib T' (mkc_qnat c).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.
Hint Resolve cequivc_qnat : slow.

Lemma per_qnat_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_qnat ts).
Proof.
  introv per ceq.
  unfold per_qnat in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_qnat_implies in ceq0; subst; GC.
  eexists; dands; spcast; eauto; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_type_value_respecting : slow.

Lemma per_bar_per_qnat_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_type_value_respecting : slow.

Lemma per_qnat_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_qnat_bar ts).
Proof.
  introv per ceq.
  unfold type_value_respecting, per_qnat_bar in *; exrepnd; GC.
  eexists; dands; eauto.
  eapply in_open_bar_pres; eauto; clear per0; introv ext h; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_bar_type_value_respecting : slow.

Lemma are_same_qnats_value_respecting {o} :
  forall (lib : @library o) c t t',
    ccequivc_ext lib t t'
    -> are_same_qnats lib c t t
    -> are_same_qnats lib c t t'.
Proof.
  introv ceq h xt.
  applydup h in xt; exrepnd; eexists; dands; eauto; GC.
  applydup ceq in xt; spcast.
  apply computes_to_valc_implies_cequivc in xt0.
  eapply cequivc_trans in xt0;[|apply cequivc_sym;eauto].
  apply cequivc_sym in xt0; apply cequivc_nat_implies_computes_to_valc in xt0; auto.
Qed.
Hint Resolve are_same_qnats_value_respecting : slow.

Lemma equality_of_qnat_value_respecting {o} :
  forall (lib : @library o) c t t',
    ccequivc_ext lib t t'
    -> equality_of_qnat lib c t t
    -> equality_of_qnat lib c t t'.
Proof.
  introv ceq equ.
  unfold equality_of_qnat in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_value_respecting : slow.

Lemma equality_of_qnat_bar_value_respecting {o} :
  forall (lib : @library o) c t t',
    ccequivc_ext lib t t'
    -> equality_of_qnat_bar lib c t t
    -> equality_of_qnat_bar lib c t t'.
Proof.
  introv ceq equ.
  eapply in_open_bar_pres; eauto; clear equ; introv ext equ; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_value_respecting : slow.

Lemma per_qnat_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_qnat_bar ts).
Proof.
  introv h e ceq.
  unfold per_qnat_bar in *; exrepnd; spcast.
  apply h0 in e; apply h0; clear h0; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_bar_term_value_respecting : slow.

Lemma per_qnat_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_qnat ts).
Proof.
  introv pera perb.
  unfold per_qnat in *; exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_qnat_implies in ceq; subst; GC.
  eexists; dands; spcast; eauto.
Qed.
Hint Resolve per_qnat_type_transitive : slow.

Lemma per_bar_per_qnat_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_type_transitive : slow.

Lemma per_qnat_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_qnat_bar ts).
Proof.
  introv per1 per2.
  unfold type_transitive, per_qnat_bar in *; exrepnd.
 assert (c0 = c) by (eapply in_open_bar_mkc_qnat_implies_same_cond; eauto); subst.
 eexists; dands; eauto.
Qed.
Hint Resolve per_qnat_bar_type_transitive : slow.

Lemma are_same_qnats_trans {o} :
  forall lib c (t1 t2 t3 : @CTerm o),
    are_same_qnats lib c t1 t2
    -> are_same_qnats lib c t2 t3
    -> are_same_qnats lib c t1 t3.
Proof.
  introv equa equb ext.
  applydup equa in ext.
  applydup equb in ext.
  exrepnd.
  ccomputes_to_eqval.
  eexists; dands; spcast; eauto.
Qed.
Hint Resolve are_same_qnats_trans : slow.

Lemma equality_of_qnat_trans {o} :
  forall lib c (t1 t2 t3 : @CTerm o),
    equality_of_qnat lib c t1 t2
    -> equality_of_qnat lib c t2 t3
    -> equality_of_qnat lib c t1 t3.
Proof.
  introv equa equb.
  unfold equality_of_qnat in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_trans : slow.

Lemma equality_of_qnat_bar_trans {o} :
  forall lib c (t1 t2 t3 : @CTerm o),
    equality_of_qnat_bar lib c t1 t2
    -> equality_of_qnat_bar lib c t2 t3
    -> equality_of_qnat_bar lib c t1 t3.
Proof.
  introv equa equb.
  eapply in_open_bar_comb; try exact equb; clear equb.
  eapply in_open_bar_pres; try exact equa; clear equa.
  introv ext equa equb; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_trans : slow.

Lemma per_qnat_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_qnat_bar ts).
Proof.
  introv per i j.
  unfold per_qnat_bar in per; exrepnd.
  apply per0 in i; apply per0 in j; apply per0; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_bar_term_transitive : slow.

Lemma per_qnat_type_system {p} :
  forall (ts : cts(p)), type_system (per_qnat_bar ts).
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
  forall lib c (T T' : @CTerm o),
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_qnat c)
    -> T' ===>(lib) (mkc_qnat c).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma equality_of_qnat_bar_monotone {o} :
  forall {lib' lib : @library o} (ext : lib_extends lib' lib) c t1 t2,
    equality_of_qnat_bar lib c t1 t2
    -> equality_of_qnat_bar lib' c t1 t2.
Proof.
  introv ext h; eauto 3 with slow.
  eapply sub_per_equality_of_qnat_bar; eauto.
Qed.
Hint Resolve equality_of_qnat_bar_monotone : slow.

Lemma per_bar_eq_equality_of_qnat_bar_lib_per {o} :
  forall (lib : @library o) c,
    (per_bar_eq lib (equality_of_qnat_bar_lib_per lib c))
    <=2=> (equality_of_qnat_bar lib c).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.
  apply in_ext_ext_implies_in_open_bar_ext; introv; simpl; eauto 3 with slow.
Qed.

Lemma per_qnat_bar_implies_close {o} :
  forall (ts : cts(o)) uk lib T T' eq,
    per_qnat_bar (close ts) uk lib T T' eq
    -> close ts uk lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_qnat_bar in per; exrepnd.
  exists (equality_of_qnat_bar_lib_per lib c).
  dands; eauto 3 with slow.

  - eapply in_open_bar_ext_comb2;try exact per1; clear per1.
    eapply in_open_bar_ext_comb2;try exact per2; clear per2.
    apply in_ext_ext_implies_in_open_bar_ext; introv pre2 per1.
    apply CL_qnat.
    unfold per_qnat; dands; auto.
    eexists; dands; eauto.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_qnat_bar_lib_per.
Qed.

(*
Lemma type_equality_respecting_trans1_per_qnat_bar_implies {o} :
  forall (ts : cts(o)) lib T T' c,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_qnat c)
    -> ccomputes_to_valc_ext lib T' (mkc_qnat c)
    -> type_equality_respecting_trans1 (per_qnat_bar (close ts)) lib T T'
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_qnat_bar_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; eauto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_qnat in ceq; auto; spcast.
    dclose_lr; auto.
Qed.
Hint Resolve type_equality_respecting_trans1_per_qnat_bar_implies : slow.
*)

(*
Lemma type_equality_respecting_trans2_per_qnat_bar_implies {o} :
  forall (ts : cts(o)) lib T T',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T mkc_qnat
    -> ccomputes_to_valc_ext lib T' mkc_qnat
    -> type_equality_respecting_trans2 (per_qnat_bar (close ts)) lib T T'
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_qnat_bar_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.
Hint Resolve type_equality_respecting_trans2_per_qnat_bar_implies : slow.
*)

Lemma per_bar_per_qnat_implies_close {o} :
  forall (ts : cts(o)) uk lib T T' eq,
    per_bar (per_qnat (close ts)) uk lib T T' eq
    -> close ts uk lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb;try exact per1; clear per1.
  apply in_ext_ext_implies_in_open_bar_ext; introv pre1.
  apply CL_qnat; auto.
Qed.

Lemma type_equality_respecting_trans1_per_qnat_bar_implies {o} :
  forall (ts : cts(o)) uk lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_qnat n)
    -> ccomputes_to_valc_ext lib T' (mkc_qnat n')
    -> type_equality_respecting_trans1 (per_bar (per_qnat (close ts))) uk lib T T'
    -> type_equality_respecting_trans1 (close ts) uk lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_bar_per_qnat_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_computes_to_valc_qnat in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_qnat in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_qnat in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_computes_to_valc_qnat in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_per_qnat_bar_implies {o} :
  forall (ts : cts(o)) uk lib T T' n n',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_qnat n)
    -> ccomputes_to_valc_ext lib T' (mkc_qnat n')
    -> type_equality_respecting_trans2 (per_bar (per_qnat (close ts))) uk lib T T'
    -> type_equality_respecting_trans2 (close ts) uk lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_bar_per_qnat_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.

Lemma per_qnat_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_qnat ts).
Proof.
  introv pera perb.
  unfold per_qnat in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw pera0; clear pera0.

  unfold equality_of_qnat_bar in *; exrepnd.
  eapply in_open_bar_pres; eauto; clear perb; introv ext perb.
  unfold equality_of_qnat in *; exrepnd; dands; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_term_symmetric : slow.

Lemma per_bar_per_qnat_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_term_symmetric : slow.

Lemma per_qnat_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_qnat ts).
Proof.
  introv per e1 e2.
  unfold per_qnat in *; exrepnd.
  spcast; repeat computes_to_eqval.
  allrw per0; clear per0; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_term_transitive : slow.

Lemma per_bar_per_qnat_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_term_transitive : slow.

Lemma per_qnat_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_qnat ts).
Proof.
  introv per e ceq.
  unfold per_qnat in *; exrepnd.
  allrw per0; clear per0; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_term_value_respecting : slow.

Lemma per_bar_per_qnat_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_bar (per_qnat ts)).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve per_qnat_term_value_respecting : slow.

Lemma per_bar_per_qnat_type_system {p} :
  forall (ts : cts(p)), type_system (per_bar (per_qnat ts)).
Proof.
  intros; unfold type_system; sp; eauto 3 with slow.
Qed.
Hint Resolve per_bar_per_qnat_type_system : slow.

Lemma per_bar_per_qnat_uniquely_valued2 {p} :
  forall (ts : cts(p)), uniquely_valued2 (per_bar (per_qnat ts)).
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
  unfold per_qnat in *; exrepnd; spcast.

  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_qnat_implies in ceq; subst; GC.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  introv; tcsp.
Qed.
Hint Resolve per_bar_per_qnat_uniquely_valued2 : slow.
