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
Require Export nuprl_mon_func2.

Require Export close_util_int.
Require Export close_util_nat.
Require Export close_util_qnat.
Require Export close_util_atom.
Require Export close_util_uatom.
Require Export close_util_base.
Require Export close_util_csname.
Require Export close_util_approx.
Require Export close_util_cequiv.
Require Export close_util_eq.
Require Export close_util_func.
Require Export close_util_union.
Require Export close_util_image.
Require Export close_util_set.
Require Export close_util_product.
Require Export close_util_qtime.
Require Export close_util_ffdefs.


Lemma type_sys_props4_implies_eq_term_equals {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2,
    type_sys_props4 ts lib T T1 eq1
    -> ts lib T T2 eq2
    -> eq1 <=2=> eq2.
Proof.
  introv tsp eqt.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply uv; eauto.
Qed.

Lemma type_sys_props4_implies_ts {o} :
  forall (ts : cts(o)) (lib : library) (T1 T2 : CTerm) eq,
    type_sys_props4 ts lib T1 T2 eq -> ts lib T1 T2 eq.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_ts {o} :
  forall (ts : cts(o)) (lib : library) (bar : BarLib lib) (T1 T2 : CTerm) eq,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' T1 T2 (eq lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' T1 T2 (eq lib' x)).
Proof.
  introv h br ext; introv.
  apply type_sys_props4_implies_ts; eapply h; eauto 3 with slow.
Qed.

Lemma in_open_bar_ext_type_sys_props4_implies_ts {o} :
  forall (ts : cts(o)) (lib : library) (T1 T2 : CTerm) eq,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' T1 T2 (eq lib' x))
    -> in_open_bar_ext lib (fun lib' x => ts lib' T1 T2 (eq lib' x)).
Proof.
  introv h; eapply in_open_bar_ext_pres; eauto; clear h; introv h.
  apply type_sys_props4_implies_ts; eapply h; eauto 3 with slow.
Qed.

Lemma all_in_bar_close_int {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_int))
    -> all_in_bar_ext bar (fun lib' x => per_int_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma in_open_bar_close_int {o} :
  forall (lib : @library o) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar lib (fun lib => (T) ===>(lib) (mkc_int))
    -> in_open_bar_ext lib (fun lib' x => per_int_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb2; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_nat {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_Nat))
    -> all_in_bar_ext bar (fun lib' x => per_nat_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma in_open_bar_close_nat {o} :
  forall (lib : @library o) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar lib (fun lib => (T) ===>(lib) (mkc_Nat))
    -> in_open_bar_ext lib (fun lib' x => per_nat_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb2; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_qnat {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_qnat))
    -> all_in_bar_ext bar (fun lib' x => per_qnat_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma in_open_bar_close_qnat {o} :
  forall (lib : @library o) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar lib (fun lib => (T) ===>(lib) (mkc_qnat))
    -> in_open_bar_ext lib (fun lib' x => per_qnat_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb2; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_csname {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa n,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_csname n))
    -> all_in_bar_ext bar (fun lib' x => per_bar (per_csname (close ts)) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma in_open_bar_close_csname {o} :
  forall (lib : @library o) ts T T' eqa n,
    type_system ts
    -> defines_only_universes ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar lib (fun lib => (T) ===>(lib) (mkc_csname n))
    -> in_open_bar_ext lib (fun lib' x => per_bar (per_csname (close ts)) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb2; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_atom {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_atom))
    -> all_in_bar_ext bar (fun lib' x => per_atom_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma in_open_bar_close_atom {o} :
  forall (lib : @library o) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar lib (fun lib => (T) ===>(lib) (mkc_atom))
    -> in_open_bar_ext lib (fun lib' x => per_atom_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb2; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_uatom {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_uatom))
    -> all_in_bar_ext bar (fun lib' x => per_uatom_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma in_open_bar_close_uatom {o} :
  forall (lib : @library o) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar lib (fun lib => (T) ===>(lib) (mkc_uatom))
    -> in_open_bar_ext lib (fun lib' x => per_uatom_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb2; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_base {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_base))
    -> all_in_bar_ext bar (fun lib' x => per_base_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma in_open_bar_close_base {o} :
  forall (lib : @library o) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar lib (fun lib => (T) ===>(lib) (mkc_base))
    -> in_open_bar_ext lib (fun lib' x => per_base_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb2; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_eq_term_equals_implies {o} :
  forall {lib} (bar : @BarLib o lib) (eqa eqb : ext-per(lib,o)) t1 t2,
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqa lib' x t1 t2)
    -> all_in_bar_ext bar (fun lib' x => eqb lib' x t1 t2).
Proof.
  introv alla allb br ext; introv.
  eapply alla; eauto 3 with slow.
  eapply allb; eauto 3 with slow.
Qed.

Lemma in_open_bar_bar_eq_term_equals_implies {o} :
  forall (lib : @library o) (eqa eqb : ext-per(lib,o)) t1 t2,
    in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => eqa lib' x t1 t2)
    -> in_open_bar_ext lib (fun lib' x => eqb lib' x t1 t2).
Proof.
  introv alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  apply alla; auto.
Qed.

(*Lemma all_in_bar_close_approx {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)) a b,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> T ==b==>(bar) (mkc_approx a b)
    -> per_bar (per_approx_bar (close ts)) lib T T' (per_bar_eq bar eqa).
Proof.
  introv tsts dou alla allb.
  eapply local_per_bar; eauto 3 with slow.
  introv br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  simpl in *; spcast.
  apply (implies_computes_to_valc_seq_bar_raise_bar _ x) in allb.
  dclose_lr; auto.
Qed.*)

(*Lemma all_in_bar_close_cequiv {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)) a b,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> T ==b==>(bar) (mkc_cequiv a b)
    -> per_bar (per_cequiv_bar (close ts)) lib T T' (per_bar_eq bar eqa).
Proof.
  introv tsts dou alla allb.
  eapply local_per_bar; eauto 3 with slow.
  introv br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  simpl in *; spcast.
  apply (implies_computes_to_valc_seq_bar_raise_bar _ x) in allb.
  dclose_lr; auto.
Qed.*)

Lemma per_int_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_int (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_int in *; exrepnd.
  exists (equality_of_int_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_int.
    unfold per_int; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_int_bar_lib_per.
Qed.
Hint Resolve per_int_implies_per_bar : slow.

Lemma per_nat_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_nat (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_nat in *; exrepnd.
  exists (equality_of_nat_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_nat.
    unfold per_nat; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_nat_bar_lib_per.
Qed.
Hint Resolve per_nat_implies_per_bar : slow.

Lemma per_qnat_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_qnat (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_qnat in *; exrepnd.
  exists (equality_of_qnat_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_qnat.
    unfold per_qnat; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_qnat_bar_lib_per.
Qed.
Hint Resolve per_qnat_implies_per_bar : slow.

Lemma per_csname_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_csname (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists (equality_of_csname_bar_lib_per lib n).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_csname.
    exists n; repnd; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_csname_bar_lib_per.
Qed.
Hint Resolve per_csname_implies_per_bar : slow.

Lemma per_atom_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_atom (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_atom in *; exrepnd.
  exists (equality_of_atom_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_atom.
    unfold per_atom; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_atom_bar_lib_per.
Qed.
Hint Resolve per_atom_implies_per_bar : slow.

Lemma per_uatom_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_uatom (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_uatom in *; exrepnd.
  exists (equality_of_uatom_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_uatom.
    unfold per_uatom; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_uatom_bar_lib_per.
Qed.
Hint Resolve per_uatom_implies_per_bar : slow.

Lemma per_base_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_base (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_base in *; exrepnd.
  exists (per_base_eq_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_base.
    unfold per_base; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_per_base_eq_lib_per.
Qed.
Hint Resolve per_base_implies_per_bar : slow.

Lemma per_approx_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_approx (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (per_approx_eq_bar_lib_per lib a b).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_approx.
    unfold per_approx; dands; auto.
    exists a b c d; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_approx_eq_bar_lib_per.
Qed.
Hint Resolve per_approx_implies_per_bar : slow.

Lemma per_cequiv_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_cequiv (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (per_cequiv_eq_bar_lib_per lib a b).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_cequiv.
    unfold per_cequiv; dands; auto.
    exists a b c d; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_cequiv_eq_bar_lib_per.
Qed.
Hint Resolve per_cequiv_implies_per_bar : slow.

Lemma per_eq_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_eq in *; exrepnd.
  exists (eq_per_eq_bar_lib_per lib a1 a2 eqa).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_eq.
    unfold per_eq; dands; auto.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa e); dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per0.
    apply eq_term_equals_sym; apply per_bar_eq_eq_per_eq_bar_lib_per.
Qed.
Hint Resolve per_eq_implies_per_bar : slow.

Lemma local_per_func_ext_eq_trivial_bar {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    per_bar_eq lib (per_func_ext_eq_lib_per eqa eqb) t1 t2
    -> per_func_ext_eq lib eqa eqb t1 t2.
Proof.
  introv alla.
  apply per_bar_eq_per_func_ext_eq_lib_per in alla; auto.
Qed.

Lemma per_func_ext_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_func_ext (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq_lib_per eqa eqb).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_func.
    unfold per_func_ext; dands; auto.
    exists (raise_lib_per eqa e) (raise_lib_per_fam eqb e); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_func_ext_eq_lib_per.
Qed.
Hint Resolve per_func_ext_implies_per_bar : slow.

Lemma local_per_union_eq_bar {o} :
  forall (lib : @library o) (eqa eqb : lib-per(lib,o)) t1 t2,
    per_bar_eq lib (per_union_eq_bar_lib_per eqa eqb) t1 t2
    -> per_union_eq_bar lib eqa eqb t1 t2.
Proof.
  introv alla.
  apply per_bar_eq_per_union_eq_bar_lib_per in alla; auto.
Qed.

Lemma per_union_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_union (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_union in *; exrepnd.

  exists (per_union_eq_bar_lib_per eqa eqb).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_union.
    unfold per_union; dands; auto.
    exists (raise_lib_per eqa e) (raise_lib_per eqb e); dands; eauto 3 with slow.
    exists A1 A2 B1 B2; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_union_eq_bar_lib_per.
Qed.
Hint Resolve per_union_bar_implies_per_bar : slow.

Lemma local_per_qtime_eq_bar {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) t1 t2,
    per_bar_eq lib (per_qtime_eq_bar_lib_per eqa) t1 t2
    -> per_qtime_eq_bar lib eqa t1 t2.
Proof.
  introv alla.
  apply per_bar_eq_per_qtime_eq_bar_lib_per in alla; auto.
Qed.

Lemma per_qtime_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_qtime (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_qtime in *; exrepnd.

  exists (per_qtime_eq_bar_lib_per eqa).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_qtime.
    unfold per_qtime; dands; auto.
    exists (raise_lib_per eqa e) A B; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_qtime_eq_bar_lib_per.
Qed.
Hint Resolve per_qtime_bar_implies_per_bar : slow.

Lemma local_per_image_eq_bar {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) f t1 t2,
    per_bar_eq lib (per_image_eq_bar_lib_per lib eqa f) t1 t2
    -> per_image_eq_bar lib eqa f t1 t2.
Proof.
  introv alla.
  apply per_bar_eq_per_image_eq_bar_lib_per in alla; auto.
Qed.

Lemma per_image_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_image (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_image in *; exrepnd.

  exists (per_image_eq_bar_lib_per lib eqa f1).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_image.
    unfold per_image; dands; auto.
    exists (raise_lib_per eqa e); dands; eauto 3 with slow.
    exists A1 A2 f1 f2; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_image_eq_bar_lib_per.
Qed.
Hint Resolve per_image_bar_implies_per_bar : slow.

Lemma local_per_set_eq_bar_trivial_bar {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    per_bar_eq lib (per_set_eq_bar_lib_per eqa eqb) t1 t2
    -> per_set_eq_bar lib eqa eqb t1 t2.
Proof.
  introv alla.
  apply per_bar_eq_per_set_eq_bar_lib_per in alla; auto.
Qed.

Lemma per_set_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_set (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_set in *; exrepnd.

  exists (per_set_eq_bar_lib_per eqa eqb).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_set.
    unfold per_set; dands; auto.
    exists (raise_lib_per eqa e) (raise_lib_per_fam eqb e); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_set_eq_bar_lib_per.
Qed.
Hint Resolve per_set_implies_per_bar : slow.

Lemma local_per_product_bar_eq_trivial_bar {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    per_bar_eq lib (per_product_eq_bar_lib_per eqa eqb) t1 t2
    -> per_product_eq_bar lib eqa eqb t1 t2.
Proof.
  introv alla.
  apply per_bar_eq_per_product_eq_bar_lib_per in alla; auto.
Qed.

Lemma per_product_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_product_bar (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar_lib_per eqa eqb).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_product.
    unfold per_product_bar; dands; auto.
    exists (raise_lib_per eqa e) (raise_lib_per_fam eqb e); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_product_eq_bar_lib_per.
Qed.
Hint Resolve per_product_bar_implies_per_bar : slow.

Definition ts_implies_per_bar {o} (ts : cts(o)) :=
  forall lib (T T' : @CTerm o) eq,
    ts lib T T' eq
    -> per_bar ts lib T T' eq.

Definition per_bar_lib_per
           {o}
           {ts}
           {lib : @library o}
           {T T'}
           {eq : per}
           (p : per_bar ts lib T T' eq) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => eq).
  repeat introv; tcsp.
Defined.

Lemma per_bar_implies_eq_term_equals_per_bar_eq_per_bar_lib_per {o} :
  forall (ts : cts(o)) lib T T' eq (p : per_bar ts lib T T' eq),
    eq <=2=> (per_bar_eq lib (per_bar_lib_per p)).
Proof.
  repeat introv; split; introv h.

  - unfold per_bar_eq, per_bar_lib_per; simpl.
    unfold per_bar in p; exrepnd.
    apply in_ext_ext_implies_in_open_bar_ext; introv x; simpl in *; auto.

  - unfold per_bar_eq, per_bar_lib_per in h; simpl in *.
    pose proof (h lib (lib_extends_refl lib)) as h; exrepnd.
    unfold per_bar in p; exrepnd.
    pose proof (h1 _ (lib_extends_refl lib'')) as q; simpl in *; autodimp q hyp.
Qed.

Lemma in_ext_ext_prod_implies {o} :
  forall (lib : @library o) (F G : forall lib' (x : lib_extends lib' lib), Prop),
    in_ext_ext lib (fun lib' x => F lib' x # G lib' x)
    -> (in_ext_ext lib F # in_ext_ext lib G).
Proof.
  introv h; dands; introv; apply h.
Qed.

Lemma implies_eq_term_equals_per_bar_eq_trivial_bar_mon {o} :
  forall (ts : cts(o)) lib T T' eq (eqa : lib-per(lib,o)),
    uniquely_valued ts
    -> per_bar ts lib T T' eq
    -> (forall lib' x, per_bar ts lib' T T' (eqa lib' x) # sub_per eq (eqa lib' x) # sub_lib_per eqa x)
    -> (eq) <=2=> (per_bar_eq lib eqa).
Proof.
  introv uv per imp; introv; split; intro h.

  - unfold per_bar_eq; simpl.
    apply in_ext_ext_implies_in_open_bar_ext; simpl in *; introv.
    pose proof (imp _ e) as imp; repnd.
    apply imp1 in h; auto.

  - unfold per_bar_eq, per_bar_lib_per in h; simpl in *.
    unfold per_bar in per; exrepnd.
    apply per0; clear per0.

    repeat (apply in_ext_ext_prod_implies in imp; repnd).

    apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv h.

    pose proof (imp0 _ e) as imp0; simpl in *.
    unfold per_bar in *; exrepnd.
    apply imp2 in h.

    apply (lib_extends_preserves_in_open_bar_ext _ _ _ e) in per1; simpl in *.
    unfold per_bar_eq in h.

    eapply in_open_bar_ext_comb; try exact h; clear h.
    eapply in_open_bar_ext_comb; try exact imp0; clear imp0.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext; introv per1 imp0 h; introv.
    eapply uv in per1; autodimp per1 hyp; try exact imp0.
    apply per1 in h.
    eapply (lib_per_cond _ eqa0); eauto.
Qed.

Lemma ts_implies_per_bar_univ {o} : @ts_implies_per_bar o univ.
Proof.
  introv u.
  unfold univ in *; exrepnd.

  applydup @per_bar_monotone_func2 in u; exrepnd.
  exists eq'.
  dands;[|eapply implies_eq_term_equals_per_bar_eq_trivial_bar_mon; eauto; eauto 3 with slow].

  apply in_ext_ext_implies_in_open_bar_ext; introv.
  apply u1.
Qed.
Hint Resolve ts_implies_per_bar_univ : slow.

Lemma per_ffdefs_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_ffdefs (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_ffdefs in *; exrepnd.
  exists (per_ffdefs_eq_bar_lib_per eqa x1).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_ffdefs.
    unfold per_ffdefs; dands; auto.
    exists A1 A2 x1 x2 (raise_lib_per eqa e); dands; auto; eauto 3 with slow.
    introv; unfold raise_lib_per, raise_ext_per; simpl; eauto.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_ffdefs_eq_bar_lib_per.
Qed.
Hint Resolve per_ffdefs_implies_per_bar : slow.

Lemma close_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    ts_implies_per_bar ts
    -> close ts lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv tib cl.
  close_cases (induction cl using @close_ind') Case; introv; auto; eauto 3 with slow.

  Case "CL_init".
  rename_hyp_with ts tsts.
  apply tib in tsts.
  unfold per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_comb; eauto; clear tsts1.
  apply in_ext_ext_implies_in_open_bar_ext; introv tsts1.
  apply CL_init; auto.
Qed.


Definition per_bar_above {o}
           (ts    : cts(o))
           (lib   : library)
           (T1 T2 : CTerm)
           (eq    : per(o)) : [U] :=
  {eqa : lib-per(lib,o)
  , in_open_bar_ext lib (fun lib' x => ts lib' T1 T2 (eqa lib' x))
  # eq <=2=> (per_bar_eq lib eqa) }.

Definition ts_implies_per_bar_above {o} (ts : cts(o)) (lib : @library o) :=
  forall (T T' : @CTerm o) eq,
    ts lib T T' eq
    -> per_bar_above ts lib T T' eq.

Lemma per_int_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_int (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_int in *; exrepnd.
  exists (equality_of_int_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_int.
    unfold per_int; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_int_bar_lib_per.
Qed.
Hint Resolve per_int_implies_per_bar_above : slow.

Lemma per_nat_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_nat (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_nat in *; exrepnd.
  exists (equality_of_nat_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_nat.
    unfold per_nat; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_nat_bar_lib_per.
Qed.
Hint Resolve per_nat_implies_per_bar_above : slow.

Lemma per_qnat_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_qnat (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_qnat in *; exrepnd.
  exists (equality_of_qnat_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_qnat.
    unfold per_qnat; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_qnat_bar_lib_per.
Qed.
Hint Resolve per_qnat_implies_per_bar_above : slow.

Lemma per_csname_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_csname (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists (equality_of_csname_bar_lib_per lib n).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_csname.
    exists n; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_csname_bar_lib_per.
Qed.
Hint Resolve per_csname_implies_per_bar_above : slow.

Lemma per_atom_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_atom (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_atom in *; exrepnd.
  exists (equality_of_atom_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_atom.
    unfold per_atom; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_atom_bar_lib_per.
Qed.
Hint Resolve per_atom_implies_per_bar_above : slow.

Lemma per_uatom_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_uatom (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_uatom in *; exrepnd.
  exists (equality_of_uatom_bar_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_uatom.
    unfold per_uatom; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_uatom_bar_lib_per.
Qed.
Hint Resolve per_uatom_implies_per_bar_above : slow.

Lemma per_base_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_base (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_base in *; exrepnd.
  exists (per_base_eq_lib_per lib).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_base.
    unfold per_base; dands; auto; eauto 2 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    apply eq_term_equals_sym; apply per_bar_eq_per_base_eq_lib_per.
Qed.
Hint Resolve per_base_implies_per_bar_above : slow.

Lemma per_approx_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_approx (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (per_approx_eq_bar_lib_per lib a b).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_approx.
    unfold per_approx; dands; auto.
    exists a b c d; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_approx_eq_bar_lib_per.
Qed.
Hint Resolve per_approx_implies_per_bar_above : slow.

Lemma per_cequiv_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_cequiv (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (per_cequiv_eq_bar_lib_per lib a b).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_cequiv.
    unfold per_cequiv; dands; auto.
    exists a b c d; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_cequiv_eq_bar_lib_per.
Qed.
Hint Resolve per_cequiv_implies_per_bar_above : slow.

Lemma per_eq_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_eq in *; exrepnd.
  exists (eq_per_eq_bar_lib_per lib a1 a2 eqa).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_eq.
    unfold per_eq; dands; auto.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa e); dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per0.
    apply eq_term_equals_sym; apply per_bar_eq_eq_per_eq_bar_lib_per.
Qed.
Hint Resolve per_eq_implies_per_bar_above : slow.

Lemma per_func_ext_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_func_ext (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq_lib_per eqa eqb).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_func.
    unfold per_func_ext; dands; auto.
    exists (raise_lib_per eqa e) (raise_lib_per_fam eqb e); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_func_ext_eq_lib_per.
Qed.
Hint Resolve per_func_ext_implies_per_bar_above : slow.

Lemma per_product_bar_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_product_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar_lib_per eqa eqb).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_product.
    unfold per_product_bar; dands; auto.
    exists (raise_lib_per eqa e) (raise_lib_per_fam eqb e); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_product_eq_bar_lib_per.
Qed.
Hint Resolve per_product_bar_implies_per_bar_above : slow.

Lemma per_union_bar_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_union (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_union in *; exrepnd.

  exists (per_union_eq_bar_lib_per eqa eqb).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_union.
    unfold per_union; dands; auto.
    exists (raise_lib_per eqa e) (raise_lib_per eqb e); dands; eauto 3 with slow.
    exists A1 A2 B1 B2; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_union_eq_bar_lib_per.
Qed.
Hint Resolve per_union_bar_implies_per_bar_above : slow.

Lemma per_image_bar_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_image (close ts) lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_image in *; exrepnd.

  exists (per_image_eq_bar_lib_per lib eqa f1).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_image.
    unfold per_image; dands; auto.
    exists (raise_lib_per eqa e); dands; eauto 3 with slow.
    exists A1 A2 f1 f2; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_per_image_eq_bar_lib_per.
Qed.
Hint Resolve per_image_bar_implies_per_bar_above : slow.

Lemma per_bar_implies_per_bar_above {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_bar ts lib T T' eq
    -> per_bar_above ts lib T T' eq.
Proof.
  introv per.
  unfold per_bar in *; exrepnd.

  exists eqa.
  dands; auto.
Qed.
Hint Resolve per_bar_implies_per_bar_above : slow.

Lemma close_implies_per_bar_above {o} :
  forall ts (lib : @library o) (T T' : @CTerm o) eq,
    ts_implies_per_bar_above ts lib
    -> close ts lib T T' eq
    -> per_bar_above (close ts) lib T T' eq.
Proof.
  introv tib cl.
  close_cases (induction cl using @close_ind') Case; introv; auto; eauto 3 with slow.

  {
    Case "CL_init".
    rename_hyp_with ts tsts.
    apply tib in tsts.
    unfold per_bar_above in *; exrepnd.
    exists eqa; dands; auto.
    eapply in_open_bar_ext_pres; eauto; clear tsts1; introv tsts1.
    apply CL_init; auto.
  }
Qed.


(*Lemma per_bar_eq_intersect_bars_left {o} :
  forall {lib} (bar1 bar2 : @BarLib o lib) eqa a b,
    per_bar_eq lib eqa a b
    -> per_bar_eq (intersect_bars bar1 bar2) eqa a b.
Proof.
  introv h br ex; introv.
  simpl in *; exrepnd.
  eapply h; eauto 3 with slow.
Qed.*)

(*Lemma per_bar_eq_intersect_bars_right {o} :
  forall {lib} (bar1 bar2 : @BarLib o lib) eqa a b,
    per_bar_eq bar1 eqa a b
    -> per_bar_eq (intersect_bars bar2 bar1) eqa a b.
Proof.
  introv h br ex; introv.
  simpl in *; exrepnd.
  eapply h; eauto 3 with slow.
Qed.*)

Lemma ts_implies_per_bar_above_implies_ts_implies_per_bar {o} :
  forall (ts : cts(o)) lib,
    ts_implies_per_bar ts
    -> ts_implies_per_bar_above ts lib.
Proof.
  introv tsi h.
  apply tsi in h; eauto 3 with slow.
Qed.
Hint Resolve ts_implies_per_bar_above_implies_ts_implies_per_bar : slow.

Lemma type_sys_props4_ccequivc_ext_left {o} :
  forall (ts : cts(o)) lib T1 T2 T3 eq,
    type_sys_props4 ts lib T1 T2 eq
    -> ccequivc_ext lib T1 T3
    -> ts lib T1 T3 eq.
Proof.
  introv tsp ceq.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.

Lemma type_sys_props4_change_per2 {o} :
  forall (ts : cts(o)) lib T1 T2 T3 T' eqa eqb,
    type_sys_props4 ts lib T1 T2 eqa
    -> ts lib T1 T' eqb
    -> ts lib T1 T3 eqa
    -> ts lib T1 T3 eqb.
Proof.
  introv tsp ts1 ts2.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in ts1.
  apply tys; auto.
Qed.

Lemma type_sys_props4_change_per3 {o} :
  forall (ts : cts(o)) lib T1 T2 T3 eqa eqb,
    type_sys_props4 ts lib T1 T2 eqa
    -> ts lib T2 T1 eqb
    -> ts lib T1 T3 eqa
    -> ts lib T1 T3 eqb.
Proof.
  introv tsp ts1 ts2.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs in ts1.
  apply uv in ts1.
  apply tys; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_type_value_respecting_per_bar {o} :
  forall (ts : cts(o)) (lib : @library o) T1 T2 (eqa : lib-per(lib,o)) eq,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' T1 T2 (eqa lib' x))
    -> per_bar ts lib T1 T2 eq
    ->
    forall T T3,
      (T = T1 {+} T = T2)
      -> ccequivc_ext lib T T3
      -> per_bar ts lib T T3 eq.
Proof.
  introv alltsp per h ceq.
  unfold per_bar in *; exrepnd.
  repndors; subst; exists eqa0; dands; auto.

  {
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp per1.
    pose proof (type_sys_props4_ccequivc_ext_left ts lib' T1 T2 T3 (eqa lib' e)) as h.
    repeat (autodimp h hyp); eauto 3 with slow.
    eapply type_sys_props4_change_per2; eauto.
  }

  {
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp per1.
    apply type_sys_props4_sym in alltsp.
    pose proof (type_sys_props4_ccequivc_ext_left ts lib' T2 T1 T3 (eqa lib' e)) as h.
    repeat (autodimp h hyp); eauto 3 with slow.
    eapply type_sys_props4_change_per3; eauto.
  }
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_type_value_respecting_per_bar : slow.

Lemma type_sys_props4_implies_type_value_respecting1 {o} :
  forall lib (ts : cts(o)) T T1 T2 T3 T4 eq eq',
    type_sys_props4 ts lib T1 T2 eq
    -> (T = T1 {+} T = T2)
    -> ccequivc_ext lib T T3
    -> (ts lib T3 T4 eq' {+} ts lib T4 T3 eq')
    -> ts lib T T4 eq'.
Proof.
  introv tsp h ceq tsts.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply tyvrt1; eauto.
Qed.

(*
Lemma per_bar_eq_intersect3bars_as2_left {o} :
  forall {lib} (bar1 bar2 bar3 : @BarLib o lib) eqa,
    (per_bar_eq (intersect3bars bar1 bar2 bar3) eqa)
    <=2=> (per_bar_eq (intersect_bars (intersect_bars bar1 bar2) bar3) eqa).
Proof.
  repeat introv; unfold per_bar_eq; split; intro h; introv br ext;
    introv; simpl in *; exrepnd.

  - pose proof (h lib') as h; autodimp h hyp.
    simpl.
    exists lib0 lib'; dands; eauto 3 with slow.
    exists lib3 lib2; dands; eauto 2 with slow.

  - pose proof (h lib') as h; autodimp h hyp.
    simpl.
    exists lib' lib3; dands; eauto 3 with slow.
    exists lib1 lib0; dands; eauto 3 with slow.
Qed.
*)

Lemma all_in_bar_ext_type_sys_props4_implies_type_value_respecting_trans_per_bar1 {o} :
  forall (ts : cts(o)) (lib : @library o) T1 T2 (eqa : lib-per(lib,o)) eq,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' T1 T2 (eqa lib' x))
    -> per_bar ts lib T1 T2 eq
    ->
    forall T T3 T4 eq',
      (T = T1 {+} T = T2)
      -> ccequivc_ext lib T T3
      -> (per_bar ts lib T3 T4 eq' {+} per_bar ts lib T4 T3 eq')
      -> per_bar ts lib T T4 eq'.
Proof.
  introv alltsp pera h ceq perb.
  unfold per_bar in *; repndors; exrepnd;
    repndors; subst; exists eqa0; dands; auto.

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_value_respecting1; eauto; eauto 3 with slow.
  }

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_value_respecting1; eauto; eauto 3 with slow.
  }

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_value_respecting1; eauto; eauto 3 with slow.
  }

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_value_respecting1; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_type_value_respecting_trans_per_bar1 : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_type_value_respecting_trans_per_bar2 {o} :
  forall (ts : cts(o)) (lib : @library o) T1 T2 (eqa : lib-per(lib,o)) eq,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' T1 T2 (eqa lib' x))
    -> per_bar ts lib T1 T2 eq
    ->
    forall T T3 T4 eq',
      (T = T1 {+} T = T2)
      -> ccequivc_ext lib T3 T4
      -> (per_bar ts lib T T3 eq' {+} per_bar ts lib T3 T eq')
      -> per_bar ts lib T T4 eq'.
Proof.
  introv alltsp pera h ceq perb.
  unfold per_bar in *; repndors; exrepnd;
    repndors; subst; exists eqa0; dands; auto.

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_equality_respecting_trans2; eauto; eauto 3 with slow.
  }

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_equality_respecting_trans2; eauto; eauto 3 with slow.
  }

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_equality_respecting_trans2; eauto; eauto 3 with slow.
  }

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply type_sys_props4_implies_type_equality_respecting_trans2; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_type_value_respecting_trans_per_bar2 : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_term_equality_symmetric2 {o} :
  forall {lib} (bar : @BarLib o lib) ts A B eqa eqb,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A B (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_symmetric (eqb lib' x)).
Proof.
  introv alla allb br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  pose proof (allb _ br _ ext x) as allb; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in allb.
  eapply eq_term_equals_preserves_term_equality_symmetric; eauto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_term_equality_symmetric2 : slow.

Lemma in_open_bar_ext_type_sys_props4_implies_term_equality_symmetric2 {o} :
  forall (lib : @library o) ts A B eqa eqb,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => ts lib' A B (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqb lib' x)).
Proof.
  introv alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in allb.
  eapply eq_term_equals_preserves_term_equality_symmetric; eauto.
Qed.
Hint Resolve in_open_bar_ext_type_sys_props4_implies_term_equality_symmetric2 : slow.

Lemma all_in_bar_ext_type_sys_props4_implies_term_equality_transitive2 {o} :
  forall {lib} (bar : @BarLib o lib) ts A B eqa eqb,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A B (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_transitive (eqb lib' x)).
Proof.
  introv alla allb br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  pose proof (allb _ br _ ext x) as allb; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in allb.
  eapply eq_term_equals_preserves_term_equality_transitive; eauto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_term_equality_transitive2 : slow.

Lemma in_open_bar_ext_type_sys_props4_implies_term_equality_transitive2 {o} :
  forall (lib : @library o) ts A B eqa eqb,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => ts lib' A B (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqb lib' x)).
Proof.
  introv alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in allb.
  eapply eq_term_equals_preserves_term_equality_transitive; eauto.
Qed.
Hint Resolve in_open_bar_ext_type_sys_props4_implies_term_equality_transitive2 : slow.

Lemma eq_term_equals_preserves_term_equality_respecting {o} :
  forall {lib} (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_respecting lib eqa1
    -> term_equality_respecting lib eqa2.
Proof.
  introv eqiff resp h ceq.
  apply eqiff in h; apply eqiff; eapply resp; eauto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_term_equality_respecting2 {o} :
  forall {lib} (bar : @BarLib o lib) ts A B eqa eqb,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' A B (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => term_equality_respecting lib' (eqb lib' x)).
Proof.
  introv alla allb br ext; introv.
  pose proof (alla _ br _ ext x) as alla; simpl in *.
  pose proof (allb _ br _ ext x) as allb; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in allb.
  eapply eq_term_equals_preserves_term_equality_respecting; eauto.
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_term_equality_respecting2 : slow.

Lemma in_open_bar_ext_type_sys_props4_implies_term_equality_respecting2 {o} :
  forall (lib : @library o) ts A B eqa eqb,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => ts lib' A B (eqb lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqb lib' x)).
Proof.
  introv alla allb.
  eapply in_open_bar_ext_comb; try exact alla; clear alla.
  eapply in_open_bar_ext_comb; try exact allb; clear allb.
  apply in_ext_ext_implies_in_open_bar_ext; introv allb alla.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in allb.
  eapply eq_term_equals_preserves_term_equality_respecting; eauto.
Qed.
Hint Resolve in_open_bar_ext_type_sys_props4_implies_term_equality_respecting2 : slow.

Lemma type_sys_props4_implies_type_symmetric1 {o} :
  forall lib (ts : cts(o)) T1 T2 T3 eq eq',
    type_sys_props4 ts lib T1 T2 eq
    -> ts lib T1 T3 eq' <=> ts lib T3 T1 eq'.
Proof.
  introv tsp; split; intro tsts;
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum;
    apply tygs; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_type_symmetric_per_bar1 {o} :
  forall (ts : cts(o)) (lib : @library o) T1 T2 (eqa : lib-per(lib,o)) eq,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' T1 T2 (eqa lib' x))
    -> per_bar ts lib T1 T2 eq
    -> forall T3 eq', per_bar ts lib T1 T3 eq' <=> per_bar ts lib T3 T1 eq'.
Proof.
  introv alltsp pera; introv; split; introv perb;
  unfold per_bar in *; repndors; exrepnd;
    repndors; subst; exists eqa0; dands; auto.

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply (type_sys_props4_implies_type_symmetric1 _ _ T1 T2); eauto 3 with slow.
  }

  {
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1.
    eapply (type_sys_props4_implies_type_symmetric1 _ _ T1 T2); eauto 3 with slow.
  }
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_type_symmetric_per_bar1 : slow.

Definition intersect4bars {o} {lib} (bar1 bar2 bar3 bar4 : @BarLib o lib) : BarLib lib :=
  intersect_bars (intersect_bars bar1 bar2) (intersect_bars bar3 bar4).

Lemma type_sys_props4_implies_type_transitive0 {o} :
  forall lib (ts : cts(o)) T T1 T2 T3 T4 eq eq1 eq2,
    type_sys_props4 ts lib T1 T2 eq
    -> (T = T1 {+} T = T2)
    -> ts lib T3 T eq1
    -> ts lib T T4 eq2
    -> ts lib T3 T4 eq1 # ts lib T3 T4 eq2.
Proof.
  introv tsp h ceq tsts.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  eapply dum; eauto.
Qed.

Lemma type_sys_props4_implies_type_transitive1 {o} :
  forall lib (ts : cts(o)) T T1 T2 T3 T4 eq eq1 eq2,
    type_sys_props4 ts lib T1 T2 eq
    -> (T = T1 {+} T = T2)
    -> ts lib T3 T eq1
    -> ts lib T T4 eq2
    -> ts lib T3 T4 eq1.
Proof.
  introv tsp h ceq tsts.
  eapply type_sys_props4_implies_type_transitive0 in tsts; eauto;tcsp.
Qed.

Lemma type_sys_props4_implies_type_transitive2 {o} :
  forall lib (ts : cts(o)) T T1 T2 T3 T4 eq eq1 eq2,
    type_sys_props4 ts lib T1 T2 eq
    -> (T = T1 {+} T = T2)
    -> ts lib T3 T eq1
    -> ts lib T T4 eq2
    -> ts lib T3 T4 eq2.
Proof.
  introv tsp h ceq tsts.
  eapply type_sys_props4_implies_type_transitive0 in tsts; eauto;tcsp.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_type_transitive_per_bar1 {o} :
  forall (ts : cts(o)) (lib : @library o) T1 T2 (eqa : lib-per(lib,o)) eq,
    in_open_bar_ext lib (fun lib' x => type_sys_props4 ts lib' T1 T2 (eqa lib' x))
    -> per_bar ts lib T1 T2 eq
    -> forall T T3 T4 eq1 eq2,
        (T = T1 {+} T = T2)
        -> per_bar ts lib T3 T eq1
        -> per_bar ts lib T T4 eq2
        -> (per_bar ts lib T3 T4 eq1 # per_bar ts lib T3 T4 eq2).
Proof.
  introv alltsp pera h perb perc; repndors; subst; dands; unfold per_bar in *; exrepnd.

  {
    exists eqa0; dands; auto.
    eapply in_open_bar_ext_comb; try exact perc1; clear perc1.
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1 perc1.
    eapply (type_sys_props4_implies_type_transitive1 _ _ T1 T1 T2); eauto.
  }

  {
    exists eqa1; dands; auto.
    eapply in_open_bar_ext_comb; try exact perc1; clear perc1.
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1 perc1.
    eapply (type_sys_props4_implies_type_transitive2 _ _ T1 T1 T2); eauto.
  }

  {
    exists eqa0; dands; auto.
    eapply in_open_bar_ext_comb; try exact perc1; clear perc1.
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1 perc1.
    eapply (type_sys_props4_implies_type_transitive1 _ _ T2 T1 T2); eauto.
  }

  {
    exists eqa1; dands; auto.
    eapply in_open_bar_ext_comb; try exact perc1; clear perc1.
    eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
    eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
    eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
    apply in_ext_ext_implies_in_open_bar_ext; introv alltsp pera1 perb1 perc1.
    eapply (type_sys_props4_implies_type_transitive2 _ _ T2 T1 T2); eauto.
  }
Qed.
Hint Resolve all_in_bar_ext_type_sys_props4_implies_type_transitive_per_bar1 : slow.
