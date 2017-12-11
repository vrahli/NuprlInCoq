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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.


Lemma type_sys_props4_implies_eq_term_equals {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2,
    type_sys_props4 ts lib T T1 eq1
    -> ts lib T T2 eq2
    -> eq1 <=2=> eq2.
Proof.
  introv tsp eqt.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply uv; eauto.
Qed.

Lemma type_sys_props4_implies_ts {o} :
  forall (ts : cts(o)) (lib : library) (T1 T2 : CTerm) eq,
    type_sys_props4 ts lib T1 T2 eq -> ts lib T1 T2 eq.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_ts {o} :
  forall (ts : cts(o)) (lib : library) (bar : BarLib lib) (T1 T2 : CTerm) eq,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' T1 T2 (eq lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' T1 T2 (eq lib' x)).
Proof.
  introv h br ext; introv.
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

Lemma all_in_bar_close_csname {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_csname))
    -> all_in_bar_ext bar (fun lib' x => per_csname_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
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
  exists (trivial_bar lib) (equality_of_int_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_int.
    unfold per_int; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_int_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_int_bar; eauto 3 with slow.
Qed.
Hint Resolve per_int_implies_per_bar : slow.

Lemma per_nat_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_nat (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_nat in *; exrepnd.
  exists (trivial_bar lib) (equality_of_nat_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_nat.
    unfold per_nat; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_nat_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_nat_bar; eauto 3 with slow.
Qed.
Hint Resolve per_nat_implies_per_bar : slow.

Lemma per_csname_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_csname (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists (trivial_bar lib) (equality_of_csname_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_csname.
    unfold per_csname in *; repnd; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_csname_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_csname_bar; eauto 3 with slow.
Qed.
Hint Resolve per_csname_implies_per_bar : slow.

Lemma per_atom_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_atom (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_atom in *; exrepnd.
  exists (trivial_bar lib) (equality_of_atom_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_atom.
    unfold per_atom; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_atom_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_atom_bar; eauto 3 with slow.
Qed.
Hint Resolve per_atom_implies_per_bar : slow.

Lemma per_uatom_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_uatom (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_uatom in *; exrepnd.
  exists (trivial_bar lib) (equality_of_uatom_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_uatom.
    unfold per_uatom; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_uatom_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_uatom_bar; eauto 3 with slow.
Qed.
Hint Resolve per_uatom_implies_per_bar : slow.

Lemma per_base_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_base (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_base in *; exrepnd.
  exists (trivial_bar lib) (per_base_eq_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_base.
    unfold per_base; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_base_bar; eauto].
    introv br ext x.
    eapply sub_per_base_eq; eauto 3 with slow.
Qed.
Hint Resolve per_base_implies_per_bar : slow.

Lemma per_approx_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_approx (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (trivial_bar lib) (per_approx_eq_bar_lib_per lib a b).
  dands.

  - introv br ext; introv.
    apply CL_approx.
    unfold per_approx; dands; auto.
    exists a b c d; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_approx_bar; eauto].
    introv br ext x.
    eapply sub_per_approx_eq_bar; eauto 3 with slow.
Qed.
Hint Resolve per_approx_implies_per_bar : slow.

Lemma per_cequiv_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_cequiv (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (trivial_bar lib) (per_cequiv_eq_bar_lib_per lib a b).
  dands.

  - introv br ext; introv.
    apply CL_cequiv.
    unfold per_cequiv; dands; auto.
    exists a b c d; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_cequiv_bar; eauto].
    introv br ext x.
    eapply sub_per_cequiv_eq_bar; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_implies_per_bar : slow.

Lemma per_eq_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_eq in *; exrepnd.
  exists (trivial_bar lib) (eq_per_eq_bar_lib_per lib a1 a2 eqa).
  dands.

  - introv br ext; introv.
    apply CL_eq.
    unfold per_eq; dands; auto.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa x); dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_eq_bar; eauto];[].
    introv br ext; introv; simpl.
    eapply sub_per_eq_per_eq_bar; eauto 3 with slow.
Qed.
Hint Resolve per_eq_implies_per_bar : slow.

Definition per_func_ext_eq_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_func_ext_eq lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).

  repeat introv.
  unfold per_func_ext_eq, raise_lib_per_fam, raise_lib_per, raise_ext_per, raise_ext_per_fam; simpl.
  split; intro h; exrepnd; introv; exists bar; introv br ext; repeat introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in h0.
    pose proof (h0 a a') as h0; simpl in *.
    assert (eqa lib'1 (lib_extends_trans x e) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    pose proof (h0 e2) as h.
    eapply (lib_per_fam_cond _ eqb); eauto.

  - pose proof (h0 _ br _ ext x) as h0; simpl in h0.
    pose proof (h0 a a') as h0; simpl in *.
    assert (eqa lib'1 (lib_extends_trans x y) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    pose proof (h0 e2) as h.
    eapply (lib_per_fam_cond _ eqb); eauto.
Defined.

Lemma local_per_func_ext_eq_trivial_bar {o} :
  forall {lib} (bar : @BarLib o lib) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    per_bar_eq bar (per_func_ext_eq_lib_per eqa eqb) t1 t2
    -> per_func_ext_eq lib eqa eqb t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (alla0 _ br _ ext0 x0) as alla0.
  unfold per_func_eq, raise_lib_per, raise_ext_per in alla0.
  introv.
  pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext _ _ br0)) a a') as alla0; simpl in *.
  assert (eqa lib'0 (lib_extends_trans (lib_extends_trans ext (bar_lib_ext (fbar lib1 br lib2 ext0 x0) lib' br0)) x0) a a') as e'.
  { eapply (lib_per_cond lib eqa); eauto. }
  pose proof (alla0 e') as alla0; simpl in *.
  unfold raise_ext_per_fam in *.
  eapply (lib_per_fam_cond _ eqb); eauto.
Qed.

Lemma per_func_ext_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_func_ext (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_func_ext in *; exrepnd.

  exists (trivial_bar lib) (per_func_ext_eq_lib_per eqa eqb).
  dands.

  - introv br ext; introv; simpl in *.
    apply CL_func.
    unfold per_func_ext; dands; auto.
    exists (raise_lib_per eqa x) (raise_lib_per_fam eqb x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    introv; simpl.
    introv; split; introv h;[|eapply local_per_func_ext_eq_trivial_bar; eauto];[].
    introv br ext; introv; simpl in *.
    eapply sub_per_per_func_ext_eq; eauto 3 with slow.
Qed.
Hint Resolve per_func_ext_implies_per_bar : slow.

Definition per_union_eq_bar_lib_per
           {o}
           {lib : @library o}
           (eqa eqb : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_union_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per eqb x)).

  repeat introv.
  unfold per_union_eq_bar, raise_lib_per, raise_ext_per; simpl.
  split; intro h; exrepnd.

  - exists bar; introv br ext; introv.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd;
      [left|right]; eexists; eexists; dands; eauto.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }

  - exists bar; introv br ext; introv.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd;
      [left|right]; eexists; eexists; dands; eauto.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }
Defined.

Lemma local_per_union_eq_bar {o} :
  forall {lib} (bar : BarLib lib) (eqa eqb : lib-per(lib,o)) t1 t2,
    per_bar_eq bar (per_union_eq_bar_lib_per eqa eqb) t1 t2
    -> per_union_eq_bar lib eqa eqb t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (alla0 _ br _ ext0 x0) as alla0.
  pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext _ _ br0))) as alla0; simpl in *.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd;
    [left|right]; eexists; eexists; dands; eauto.
  { eapply (lib_per_cond _ eqa); eauto. }
  { eapply (lib_per_cond _ eqb); eauto. }
Qed.

Lemma per_union_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_union (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_union in *; exrepnd.

  exists (trivial_bar lib) (per_union_eq_bar_lib_per eqa eqb).
  dands.

  - introv br ext; introv; simpl in *.
    apply CL_union.
    unfold per_union; dands; auto.
    exists (raise_lib_per eqa x) (raise_lib_per eqb x); dands; eauto 3 with slow.
    exists A1 A2 B1 B2; dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    introv; simpl.
    introv; split; introv h;[|eapply local_per_union_eq_bar; eauto];[].
    introv br ext; introv; simpl in *.
    eapply sub_per_per_union_eq_bar; eauto 3 with slow.
Qed.
Hint Resolve per_union_bar_implies_per_bar : slow.

Definition per_product_bar_eq_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_product_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).

  repeat introv.
  unfold per_product_eq_bar, raise_lib_per_fam, raise_lib_per, raise_ext_per, raise_ext_per_fam; simpl.
  split; intro h; exrepnd; exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold per_product_eq in *; exrepnd.
    assert (eqa lib'1 (lib_extends_trans x y) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb); eauto.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold per_product_eq in *; exrepnd.
    assert (eqa lib'1 (lib_extends_trans x e) a a') as e2.
    { eapply (lib_per_cond _ eqa); eauto. }
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb); eauto.
Defined.

Lemma local_per_product_bar_eq_trivial_bar {o} :
  forall {lib} (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) t1 t2,
    per_bar_eq (trivial_bar lib) (per_product_bar_eq_lib_per eqa eqb) t1 t2
    -> per_product_eq_bar lib eqa eqb t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (alla0 _ br _ ext0 x0) as alla0.
  pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext _ _ br0))) as alla0; simpl in *.
  unfold per_product_eq, raise_ext_per in *; exrepnd; simpl in *.
  assert (eqa lib'0 x a a') as e2.
  { eapply (lib_per_cond _ eqa); eauto. }
  exists a a' b b' e2; dands; auto.
  eapply (lib_per_fam_cond _ eqb); eauto.
Qed.

Lemma per_product_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_product_bar (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_product_bar in *; exrepnd.

  exists (trivial_bar lib) (per_product_bar_eq_lib_per eqa eqb).
  dands.

  - introv br ext; introv; simpl in *.
    apply CL_product.
    unfold per_product_bar; dands; auto.
    exists (raise_lib_per eqa x) (raise_lib_per_fam eqb x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    introv; simpl.
    introv; split; introv h;[|eapply local_per_product_bar_eq_trivial_bar; eauto];[].
    introv br ext; introv; simpl in *.
    eapply sub_per_per_product_bar_eq; eauto 3 with slow.
Qed.
Hint Resolve per_product_bar_implies_per_bar : slow.

Definition ts_implies_per_bar {o} (ts : cts(o)) :=
  forall lib (T T' : @CTerm o) eq,
    ts lib T T' eq
    -> per_bar ts lib T T' eq.

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
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (tsts0 _ br _ ext x) as tsts0; simpl in *.
  apply CL_init; auto.
Qed.

Definition per_bar_above {o}
           (ts    : cts(o))
           {lib   : library}
           (bar   : BarLib lib)
           (T1 T2 : CTerm)
           (eq    : per(o)) : [U] :=
  {bar' : BarLib lib
  , {eqa : lib-per(lib,o)
  , all_in_bar_ext (intersect_bars bar bar') (fun lib' x => ts lib' T1 T2 (eqa lib' x))
  # eq <=2=> (per_bar_eq (intersect_bars bar bar') eqa) }}.

Definition ts_implies_per_bar_above {o} {lib} (ts : cts(o)) (bar : BarLib lib) :=
  forall (T T' : @CTerm o) eq,
    ts lib T T' eq
    -> per_bar_above ts bar T T' eq.

(*Lemma per_int_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_int_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_int_bar in *; exrepnd.
  exists bar (equality_of_int_bar_lib_per lib).
  dands.

  - introv br ext; introv; simpl in *; exrepnd.
    apply CL_int.
    unfold per_int_bar; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_int_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_int_bar; eauto 3 with slow.
Qed.
Hint Resolve per_int_bar_implies_per_bar_above : slow.

Lemma per_nat_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_nat_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_nat_bar in *; exrepnd.
  exists bar (equality_of_nat_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_nat.
    unfold per_nat_bar; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_nat_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_nat_bar; eauto 3 with slow.
Qed.
Hint Resolve per_nat_bar_implies_per_bar_above : slow.

Lemma per_csname_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_csname_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_csname_bar in *; exrepnd.
  exists bar (equality_of_csname_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_csname.
    unfold per_csname_bar; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_csname_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_csname_bar; eauto 3 with slow.
Qed.
Hint Resolve per_csname_bar_implies_per_bar_above : slow.

Lemma per_atom_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_atom_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_atom_bar in *; exrepnd.
  exists bar (equality_of_atom_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_atom.
    unfold per_atom_bar; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_atom_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_atom_bar; eauto 3 with slow.
Qed.
Hint Resolve per_atom_bar_implies_per_bar_above : slow.

Lemma per_uatom_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_uatom_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_uatom_bar in *; exrepnd.
  exists bar (equality_of_uatom_bar_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_uatom.
    unfold per_uatom_bar; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_uatom_bar; eauto].
    introv br ext x.
    eapply sub_per_equality_of_uatom_bar; eauto 3 with slow.
Qed.
Hint Resolve per_uatom_bar_implies_per_bar_above : slow.

Lemma per_base_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_base_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_base_bar in *; exrepnd.
  exists bar (per_base_eq_lib_per lib).
  dands.

  - introv br ext; introv.
    apply CL_base.
    unfold per_base_bar; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per.
    unfold per_bar_eq; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_base_bar; eauto].
    introv br ext x.
    eapply sub_per_base_eq; eauto 3 with slow.
Qed.
Hint Resolve per_base_bar_implies_per_bar_above : slow.

Lemma per_approx_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_approx_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_approx_bar in *; exrepnd.
  exists bar (per_approx_eq_bar_lib_per lib a b).
  dands.

  - introv br ext; introv.
    apply CL_approx.
    unfold per_approx_bar; dands; auto.
    exists a b c d; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    unfold per_approx_eq_bar; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_approx_bar; eauto].
    introv br ext; introv.
    eapply sub_per_approx_eq_bar; eauto 3 with slow.
Qed.
Hint Resolve per_approx_bar_implies_per_bar_above : slow.

Lemma per_cequiv_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_cequiv_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_cequiv_bar in *; exrepnd.
  exists bar (per_cequiv_eq_bar_lib_per lib a b).
  dands.

  - introv br ext; introv.
    apply CL_cequiv.
    unfold per_cequiv_bar; dands; auto.
    exists a b c d; dands; auto.
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    unfold per_cequiv_eq_bar; introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_cequiv_bar; eauto].
    introv br ext; introv.
    eapply sub_per_cequiv_eq_bar; eauto 3 with slow.
Qed.
Hint Resolve per_cequiv_bar_implies_per_bar_above : slow.

Lemma per_eq_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_eq_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_eq_bar in *; exrepnd.
  exists (trivial_bar lib) (per_eq_eq_lib_per eqa a1 a2).
  dands.

  - introv br ext; introv.
    apply CL_eq.
    unfold per_eq_bar; dands; auto.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa x); dands; auto;[].
    exists (raise_bar bar0 x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_eq_bar; eauto];[].
    introv br ext; introv.
    eapply sub_per_per_eq_eq; eauto 3 with slow.
Qed.
Hint Resolve per_eq_bar_implies_per_bar_above : slow.

(*Lemma per_func_ext_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_func_ext (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_func_ext in *; exrepnd.

  exists bar (per_func_ext_eq_lib_per eqa eqb).
  dands.

  - introv br ext; introv; simpl in *.
    apply CL_func.
    unfold per_func_ext; dands; auto.
    exists (raise_lib_per eqa x) (raise_lib_per_fam eqb x); dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    introv; simpl.

    introv; split; introv h;[|eapply local_per_func_ext_eq_trivial_bar; eauto];[].
    introv br ext; introv; simpl in *.
    eapply sub_per_per_func_ext_eq; eauto 3 with slow.
Qed.
Hint Resolve per_func_ext_implies_per_bar : slow.
*)

(*Lemma close_implies_per_bar_above {o} :
  forall ts lib (bar : @BarLib o lib) (T T' : @CTerm o) eq,
    ts_implies_per_bar_above ts bar
    -> close ts lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv tib cl.
  close_cases (induction cl using @close_ind') Case; introv; auto; eauto 3 with slow.

  {
    Case "CL_init".
    rename_hyp_with ts tsts.
    apply tib in tsts.
    unfold per_bar_above in *; exrepnd.
    exists bar' eqa; dands; auto.
    introv br ext; introv.
    pose proof (tsts0 _ br _ ext x) as tsts0; simpl in *.
    apply CL_init; auto.
  }

Lemma per_bar_implies_per_bar_above {o} :
  forall ts lib (bar : BarLib lib) (T T' : @CTerm o) eq,
    per_bar (close ts) lib T T' eq
    -> per_bar_above (close ts) bar T T' eq.
Proof.
  introv per.
  unfold per_bar in *; exrepnd.
  exists bar0 eqa.
  dands.

  - introv br ext; introv.
    apply CL_bar.
    unfold per_bar; dands; auto.
    exists (raise_bar bar0 x) (raise_lib_per eqa x); dands; eauto 3 with slow.
    introv; split; intro h.

    + introv br' ext'; introv; simpl in *; exrepnd.
      unfold raise_ext_per.

  - eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv; simpl.
    introv; split; introv h;[|eapply local_equality_of_eq_bar; eauto];[].
    introv br ext; introv.
    eapply sub_per_per_eq_eq; eauto 3 with slow.
Qed.
Hint Resolve per_eq_bar_implies_per_bar_above : slow.


Qed.*)
*)

Lemma per_bar_eq_intersect_bars_left {o} :
  forall {lib} (bar1 bar2 : @BarLib o lib) eqa a b,
    per_bar_eq bar1 eqa a b
    -> per_bar_eq (intersect_bars bar1 bar2) eqa a b.
Proof.
  introv h br ex; introv.
  simpl in *; exrepnd.
  eapply h; eauto 3 with slow.
Qed.

Lemma per_bar_eq_intersect_bars_right {o} :
  forall {lib} (bar1 bar2 : @BarLib o lib) eqa a b,
    per_bar_eq bar1 eqa a b
    -> per_bar_eq (intersect_bars bar2 bar1) eqa a b.
Proof.
  introv h br ex; introv.
  simpl in *; exrepnd.
  eapply h; eauto 3 with slow.
Qed.

Lemma close_type_system_bar {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T' eq (eqa : lib-per(lib,o)),
    ts_implies_per_bar ts
    (*-> local_ts ts*)
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => type_sys_props4 (close ts) lib' T T' (eqa lib' x))
    -> (eq <=2=> (per_bar_eq bar eqa))
    -> per_bar (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tib (*locts*) tysys dou mon allcl alltsp eqiff per.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.

    eapply eq_term_equals_trans;[eauto|]; clear eqiff.

    apply eq_term_equals_sym; introv; split; intro h.

    {
      introv br ext; introv.
      pose proof (alltsp lib' br lib'0 ext x) as alltsp; simpl in *.
      apply (close_monotone _ mon _ lib'0) in cl; auto; exrepnd.
      apply cl0 in h.
      eapply type_sys_props4_implies_eq_term_equals in cl1;[|eauto].
      apply cl1; auto.
    }

    {

      assert (close ts lib T T' eq) as cl'.
      { apply CL_bar; auto. }

      (* it would be great to have the "above" version here *)
      apply close_implies_per_bar in cl;auto;[].
      unfold per_bar in cl; exrepnd.
      apply cl1; clear cl1.

      apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in alltsp.
      apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in allcl.
      apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in cl0.
      apply (per_bar_eq_intersect_bars_left _ bar0) in h.

      SearchAbout intersect_bars per_bar_eq.

XXXXXXXX
*)

      Lemma xxx {o} :
        forall ts lib (bar : @BarLib o lib) T T1 T2 eq (eqa : lib-per(lib,o)) t1 t2,
          type_system ts
          -> defines_only_universes ts
          -> all_in_bar_ext bar (fun lib' x => type_sys_props4 (close ts) lib' T T1 (eqa lib' x))
          -> all_in_bar_ext bar (fun lib' x => eqa lib' x t1 t2)
          -> close ts lib T T2 eq
          -> eq t1 t2.
      Proof.
        introv tsts dou tysys eqt cl.
        close_cases (induction cl using @close_ind') Case; introv.

        - Case "CL_init".

          (* prove that this is true about universes,
             and assume that it is true about [ts] *)
          admit.

        - Case "CL_bar".
          apply eqiff.
          introv br ext; introv.
          pose proof (reca lib' br lib'0 ext x (raise_bar bar x) (raise_lib_per eqa x)) as reca; simpl in *.
          repeat (autodimp reca hyp).

          {
            introv b e; introv.
            simpl in *; unfold raise_lib_per; exrepnd.
            eapply tysys; eauto 3 with slow.
          }

          {
            introv b e; introv.
            simpl in *; unfold raise_lib_per; exrepnd.
            eapply eqt; eauto 3 with slow.
          }

        - Case "CL_int".
          unfold per_int_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_int in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_int_bar in tysys; auto.

        - Case "CL_nat".
          unfold per_nat_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_nat in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_nat_bar in tysys; auto.

        - Case "CL_csname".
          unfold per_csname_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_csname in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_csname_bar in tysys; auto.

        - Case "CL_atom".
          unfold per_atom_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_atom in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_atom_bar in tysys; auto.

        - Case "CL_uatom".
          unfold per_uatom_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_uatom in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_uatom_bar in tysys; auto.

        - Case "CL_base".
          unfold per_base_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_base in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_base_bar in tysys; auto.

        - Case "CL_approx".
          unfold per_approx_bar in *; exrepnd.
          apply per1; clear per1.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per0.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per3.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per2.
          remember (intersect_bars bar bar0) as bar1; clear Heqbar1.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          eapply all_in_bar_close_approx in tysys; eauto.
          unfold per_bar in tysys; exrepnd.
          fold (per_bar_eq bar1 eqa t1 t2) in *.
          apply tysys1 in eqt; clear tysys1.

          apply (local_equality_of_approx_bar bar2).
          introv br ext x.
          pose proof (tysys0 lib' br lib'0 ext x) as tysys0; simpl in *.
          pose proof (eqt lib' br lib'0 ext x) as eqt; simpl in *.
          unfold per_approx_bar in tysys0; exrepnd.
          apply tysys0 in eqt; clear tysys0.
          eapply (eq_per_approx_eq_bar (intersect_bars (raise_bar bar1 x) bar3)); eauto.
          eapply two_computes_to_valc_ceq_bar_mkc_approx; eauto 3 with slow.

        - Case "CL_cequiv".
          unfold per_cequiv_bar in *; exrepnd.
          apply per1; clear per1.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per0.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per3.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per2.
          remember (intersect_bars bar bar0) as bar1; clear Heqbar1.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          eapply all_in_bar_close_cequiv in tysys; eauto.
          unfold per_bar in tysys; exrepnd.
          fold (per_bar_eq bar1 eqa t1 t2) in *.
          apply tysys1 in eqt; clear tysys1.

          apply (local_equality_of_cequiv_bar bar2).
          introv br ext x.
          pose proof (tysys0 lib' br lib'0 ext x) as tysys0; simpl in *.
          pose proof (eqt lib' br lib'0 ext x) as eqt; simpl in *.
          unfold per_cequiv_bar in tysys0; exrepnd.
          apply tysys0 in eqt; clear tysys0.
          eapply (eq_per_cequiv_eq_bar (intersect_bars (raise_bar bar1 x) bar3)); eauto.
          eapply two_computes_to_valc_ceq_bar_mkc_cequiv; eauto 3 with slow.

        - Case "CL_eq".
          clear per.
          apply eqiff; clear eqiff.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in c1.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in c2.
          apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in cla.
          apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in reca.
          apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in eos1.
          apply (implies_all_in_bar_ext_intersect_bars_right _ bar) in eos2.

          remember (intersect_bars bar bar0) as bar1; clear Heqbar1.
          fold (per_bar_eq bar1 eqa t1 t2) in *.

Lemma local_per_bar_unf {o} :
  forall {lib} (ts : cts(o)) (bar : @BarLib o lib) T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => type_extensionality_body ts lib' T T' (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => uniquely_valued_body ts lib' T T' (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => per_bar ts lib' T T' (eqa lib' x))
    -> per_bar ts lib T T' eq.
Proof.
  introv eqiff text uv alla.
  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.

  exists (bar_of_bar_fam fbar).

  apply all_in_bar_ext2_exists_eqa_implies in alla0; exrepnd.

  exists (lib_per_per_bar fbar feqa).
  dands.

  {
    introv br ext; introv.
    simpl in *; exrepnd.

    pose proof (alla1 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as b.
    pose proof (alla2
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext b lib' br0)))
      as alla2; simpl in *.

    eapply (text _ br _ (lib_extends_trans (lib_extends_trans ext (bar_lib_ext b lib' br0)) ext0) x).
    eapply (uv _ br _ (lib_extends_trans (lib_extends_trans ext (bar_lib_ext b lib' br0)) ext0) x) in alla2.
    eapply eq_term_equals_trans;[eauto|].

    introv; split; introv w.

    { subst.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    apply alla2.
    eapply uv; eauto 4 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    introv.
    unfold per_bar_eq; split; introv h br ext; introv.

    - introv.
      simpl in *; exrepnd.
      pose proof (alla1 lib1 br lib2 ext0 x0) as q; repnd.
      pose proof (h lib1 br lib2 ext0 x0) as h; simpl in *.
      apply q in h.

      clear q q0.

      exists lib1 br lib2 ext0 x0 lib' ext br0.
      eapply h; eauto.

    - pose proof (alla1 lib' br lib'0 ext x) as z; repnd.
      apply z.
      introv fb w; introv.

      pose proof (h lib'1) as h.
      simpl in h.

      autodimp h hyp.
      { exists lib' br lib'0 ext x; auto. }

      pose proof (h lib'2 w) as h; simpl in *.
      autodimp h hyp; eauto 3 with slow.
      exrepnd.

      pose proof (z0 lib'1 fb lib'2 w x0) as z0; simpl in *.

      pose proof (alla1 lib1 br0 lib2 ext0 x1) as q; repnd.
      pose proof (q0 lib0 fb0 lib'2 w0 (lib_extends_trans w0 (bar_lib_ext (fbar lib1 br0 lib2 ext0 x1) lib0 fb0))) as q0; simpl in *.
      apply (uv _ br _ (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) in z0; apply z0; auto.
      eapply (uv _ br _ (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) in q0; apply q0; auto.
  }
Qed.
Hint Resolve local_per_bar_unf : slow.

Lemma all_in_bar_close_eq {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' (eqa : lib-per(lib,o)) a b A,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> T ==b==>(bar) (mkc_equality a b A)
    -> per_bar (per_eq_bar (close ts)) lib T T' (per_bar_eq bar eqa).
Proof.
  introv tsts dou alla allb.
  eapply local_per_bar_unf; eauto 3 with slow.
  Focus 3.
  {
    introv br ext; introv.
    pose proof (alla lib' br lib'0 ext x) as alla.
    simpl in *; spcast.
    apply (implies_computes_to_valc_seq_bar_raise_bar _ x) in allb.
    dclose_lr; auto.
Qed.


          Check all_in_bar_close_cequiv.
          Locate all_in_bar_close_cequiv.

          Locate local_equality_of_approx_bar.

          Check all_in_bar_ext_type_sys_props4_implies_ts.
          Check all_in_bar_close_cequiv.
          unfold per_eq_eq, per_eq_eq1.

      Qed.

    }

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
      apply CL_int; auto;
        assert (type_symmetric (per_int_bar (close ts))) as tys
          by (apply per_int_bar_type_symmetric);
        assert (type_extensionality (per_int_bar (close ts))) as tye
            by (apply per_int_bar_type_extensionality);
        apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; sp; subst; apply CL_int;
      assert (type_value_respecting (per_int_bar (close ts)))
      as tvr by (apply per_int_bar_type_value_respecting).

    * apply tvr; auto;
        apply @type_system_type_mem with (T' := T'); auto;
          try (apply per_int_bar_type_symmetric);
          try (apply per_int_bar_type_transitive).

    * apply tvr; auto.
      apply @type_system_type_mem1 with (T := T); auto;
        try (apply per_int_bar_type_transitive);
        try (apply per_int_bar_type_symmetric).

  + SCase "type_value_respecting_trans".
    eapply type_equality_respecting_trans_per_int_bar_implies; eauto.
    apply type_system_implies_type_equality_respecting_trans.
    apply per_int_type_system.

  + SCase "term_symmetric".
    assert (term_symmetric (per_int_bar (close ts))) as tes
        by (apply per_int_bar_term_symmetric).
    eapply tes; eauto.

  + SCase "term_transitive".
    assert (term_transitive (per_int_bar (close ts))) as tet
        by (apply per_int_bar_term_transitive).
    eapply tet; eauto.

  + SCase "term_value_respecting".
    assert (term_value_respecting (per_int_bar (close ts))) as tvr
        by (apply per_int_bar_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.

    * apply per_int_bar_type_symmetric.

    * apply per_int_bar_type_transitive.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    * apply CL_int; allunfold @per_int_bar; sp.
      exists bar0; dands; auto.

    * apply CL_int; allunfold @per_int_bar; sp.
      exists bar0; dands; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive"; repdors; subst; dclose_lr;
      dands; apply CL_int; allunfold @per_int_bar; sp;
        exists (intersect_bars bar1 bar0); dands; eauto 2 with slow.
Qed.
