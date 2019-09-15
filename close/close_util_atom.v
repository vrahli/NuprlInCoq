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


Lemma per_atom_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_atom_bar ts).
Proof.
 unfold uniquely_valued, per_atom_bar, eq_term_equals; sp.
 allrw; sp.
Qed.
Hint Resolve per_atom_bar_uniquely_valued : slow.

Lemma per_atom_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_atom_bar ts).
Proof.
  unfold type_extensionality, per_atom_bar, eq_term_equals; sp.
  allrw <-; sp.
Qed.
Hint Resolve per_atom_bar_type_extensionality : slow.

Lemma per_atom_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_atom_bar ts).
Proof.
  introv h; unfold per_atom_bar in *; exrepnd; dands; auto.
Qed.
Hint Resolve per_atom_bar_type_symmetric : slow.

Lemma per_atom_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_atom_bar ts).
Proof.
  introv per1 per2.
  unfold per_atom_bar in *; exrepnd; dands; auto.
Qed.
Hint Resolve per_atom_bar_type_transitive : slow.

Lemma per_atom_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_atom_bar ts).
Proof.
  introv per ceq.
  unfold type_value_respecting, per_atom_bar in *; exrepnd.
  dands; auto;[].
  eapply in_open_bar_pres; eauto; clear per0; introv ext h; eauto 3 with slow.
Qed.
Hint Resolve per_atom_bar_type_value_respecting : slow.

Lemma per_atom_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_atom_bar ts).
Proof.
  introv; unfold term_symmetric, term_equality_symmetric, per_atom_bar.
  introv k e; repnd.
  allrw.
  apply k in e.
  unfold equality_of_atom_bar, equality_of_atom in *; exrepnd.
  apply e_all_in_ex_bar_as in e; apply e_all_in_ex_bar_as.
  eapply in_open_bar_pres; eauto; clear e; introv ext e.
  exrepnd; exists s; dands; eauto 3 with slow.
Qed.
Hint Resolve per_atom_bar_term_symmetric : slow.

(* !! MOVE to cequiv *)
Lemma cequiv_token {pp} :
  forall lib T T' s,
    @computes_to_value pp lib T (mk_token s)
    -> cequiv lib T T'
    -> computes_to_value lib T' (mk_token s).
Proof.
  sp.
  apply cequiv_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv0 in p; subst; auto.
Qed.

(* !! MOVE to cequiv *)
Lemma cequivc_token {o} :
  forall lib (t t' : @CTerm o) n,
    computes_to_valc lib t (mkc_token n)
    -> cequivc lib t t'
    -> computes_to_valc lib t' (mkc_token n).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply @cequivc_canonical_form with (t' := t') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

Lemma iscvalue_mkc_token {o} :
  forall i, @iscvalue o (mkc_token i).
Proof.
  introv; unfold iscvalue; simpl; eauto with slow.
Qed.
Hint Resolve iscvalue_mkc_token : slow.

Lemma ccequivc_ext_mkc_token_implies {o} :
  forall (lib : @library o) k1 k2,
    ccequivc_ext lib (mkc_token k1) (mkc_token k2)
    -> k1 = k2.
Proof.
  introv ceq.
  pose proof (ceq lib) as ceq; autodimp ceq hyp; eauto 3 with slow; simpl in *; spcast.
  eapply cequivc_token in ceq;[|eauto 3 with slow].
  apply computes_to_valc_isvalue_eq in ceq; eauto 3 with slow.
  eqconstr ceq; auto.
Qed.

Lemma per_atom_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_atom_bar ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_atom_bar.
  introv cts per i j.
  exrepnd.
  rw per in i; rw per in j; rw per; clear per.
  unfold equality_of_atom_bar, equality_of_atom in *; exrepnd.

  apply e_all_in_ex_bar_as in i; apply e_all_in_ex_bar_as in j; apply e_all_in_ex_bar_as.
  eapply in_open_bar_comb; try exact j; clear j.
  eapply in_open_bar_comb; try exact i; clear i.
  apply in_ext_implies_in_open_bar; introv ext i j.

  exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_token_implies in ceq; subst.
  exists s0; dands; spcast; auto.
Qed.
Hint Resolve per_atom_bar_term_transitive : slow.

Lemma per_atom_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_atom_bar ts).
Proof.
  introv h e ceq.
  unfold per_nat_bar in *; exrepnd; spcast.
  apply h in e; apply h; clear h.
  unfold equality_of_atom_bar, equality_of_atom in *.
  apply e_all_in_ex_bar_as in e; apply e_all_in_ex_bar_as.
  eapply in_open_bar_pres; eauto; clear e; introv ext e; exrepnd.
  exists s; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve per_atom_bar_term_value_respecting : slow.

Lemma per_atom_bar_type_system {p} :
  forall (ts : cts(p)), type_system (per_atom_bar ts).
Proof.
  intros; unfold type_system; sp; eauto 3 with slow.
Qed.
Hint Resolve per_atom_bar_type_system : slow.

Lemma equality_of_atom_bar_monotone {o} :
  forall {lib' lib : @library o} (ext : lib_extends lib' lib) t1 t2,
    equality_of_atom_bar lib t1 t2
    -> equality_of_atom_bar lib' t1 t2.
Proof.
  introv h; eapply sub_per_equality_of_atom_bar; eauto 3 with slow.
Qed.
Hint Resolve equality_of_atom_bar_monotone : slow.

Lemma per_bar_eq_equality_of_atom_bar_lib_per {o} :
  forall (lib : @library o),
    (per_bar_eq lib (equality_of_atom_bar_lib_per lib))
    <=2=> (equality_of_atom_bar lib).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.
  apply in_ext_ext_implies_in_open_bar_ext; introv; simpl; eauto 3 with slow.
Qed.

Lemma per_atom_bar_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_atom_bar (close ts) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_atom_bar in per; exrepnd.
  exists (equality_of_atom_bar_lib_per lib).
  dands; eauto 3 with slow.

  - eapply in_open_bar_ext_comb2;try exact per0; clear per0.
    eapply in_open_bar_ext_comb2;try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext; introv pre1 per0.
    apply CL_atom.
    unfold per_atom; dands; auto.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_atom_bar_lib_per.
Qed.

Lemma ccequivc_ext_preserves_computes_to_valc_atom {o} :
  forall lib (T T' : @CTerm o),
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T mkc_atom
    -> T' ===>(lib) mkc_atom.
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma type_equality_respecting_trans1_per_atom_bar_implies {o} :
  forall (ts : cts(o)) lib T T',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T mkc_atom
    -> ccomputes_to_valc_ext lib T' mkc_atom
    -> type_equality_respecting_trans1 (per_atom_bar (close ts)) lib T T'
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_atom_bar_implies_close.
  eapply trans; eauto.
  repndors; subst.

  - apply ccequivc_ext_preserves_computes_to_valc_atom in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_atom in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_atom in ceq; auto; spcast.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_valc_atom in ceq; auto; spcast.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_per_atom_bar_implies {o} :
  forall (ts : cts(o)) lib T T',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T mkc_atom
    -> ccomputes_to_valc_ext lib T' mkc_atom
    -> type_equality_respecting_trans2 (per_atom_bar (close ts)) lib T T'
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply per_atom_bar_implies_close.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.
