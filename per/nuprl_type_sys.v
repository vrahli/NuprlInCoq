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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export close_type_sys.
Require Export Peano.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ *)
(** printing ~=~  $\sim$ *)
(** printing ===>  $\Downarrow$ *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(* begin hide *)


Lemma implies_computes_to_uni {o} :
  forall lib (T : @CTerm o) i,
    computes_to_valc lib T (mkc_uni i)
    -> computes_to_uni lib T.
Proof.
  introv comp.
  exists (trivial_bar lib).
  apply in_ext_implies_all_in_bar_trivial_bar.
  introv x.
  exists i; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_uni : slow.

Lemma defines_only_universes_univi {o} :
  forall i, @defines_only_universes o (univi i).
Proof.
  unfold defines_only_universes; sp.
  allrw @univi_exists_iff; sp; spcast; eauto 3 with slow.
Qed.
Hint Resolve defines_only_universes_univi : slow.

Lemma defines_only_universes_univi_bar {o} :
  forall i, @defines_only_universes o (univi_bar i).
Proof.
  introv u.
  unfold univi_bar, per_bar in u; exrepnd.
  exists bar.
  introv br ext.

  assert (lib_extends lib'0 lib) as x by eauto 3 with slow.
  pose proof (u0 _ br _ ext x) as per0; simpl in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  exists j; auto.
Qed.
Hint Resolve defines_only_universes_univi_bar : slow.

Lemma defines_only_universes_univ {o} :
  @defines_only_universes o univ.
Proof.
  unfold defines_only_universes, univ, univ_ex; introv per.
  unfold per_bar in *; exrepnd.
  exists bar.
  introv br ext.

  assert (lib_extends lib'0 lib) as x by eauto 3 with slow.
  pose proof (per0 _ br _ ext x) as per0; simpl in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  exists j; auto.
Qed.
Hint Resolve defines_only_universes_univ : slow.


(* end hide *)

(**

  We prove that all the Nuprl universes satisfy the type system
  properties.

*)

Lemma ccequivc_ext_uni {o} :
  forall lib (T T' : @CTerm o) i,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc lib T (mkc_uni i)
    -> ccomputes_to_valc lib T' (mkc_uni i).
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_uni in ceq';[|eauto]; exrepnd; auto.
Qed.

Lemma per_bar_univi_uniquely_valued {o} :
  forall i lib (T T' : @CTerm o) eq1 eq2,
    per_bar (univi i) lib T T' eq1
    -> per_bar (univi i) lib T T' eq2
    -> eq1 <=2=> eq2.
Proof.
  introv u v.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  eapply eq_term_equals_trans;[|apply (per_bar_eq_intersect_bars_left _ bar0)].
  eapply eq_term_equals_trans;[apply eq_term_equals_sym;apply (per_bar_eq_intersect_bars_right _ bar)|].

  unfold per_bar_eq; introv; split; intro h.

  - introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *; exrepnd.
    exists bar'.

    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.

    pose proof (u0 _ br2 _ (lib_extends_trans x0 (lib_extends_trans ext br1)) (lib_extends_trans x0 x)) as u0.
    pose proof (v0 _ br0 _ (lib_extends_trans x0 (lib_extends_trans ext br3)) (lib_extends_trans x0 x)) as v0.
    simpl in *.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_eqval.
    apply v2; apply u2; auto.

  - introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *; exrepnd.
    exists bar'.

    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.

    pose proof (u0 _ br2 _ (lib_extends_trans x0 (lib_extends_trans ext br1)) (lib_extends_trans x0 x)) as u0.
    pose proof (v0 _ br0 _ (lib_extends_trans x0 (lib_extends_trans ext br3)) (lib_extends_trans x0 x)) as v0.
    simpl in *.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_eqval.
    apply u2; apply v2; auto.
Qed.

Lemma uniquely_valued_univi {o} :
  forall i, @uniquely_valued o (univi i).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd; spcast.
  computes_to_eqval.
  eapply eq_term_equals_trans;[eauto|].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve uniquely_valued_univi : slow.

Lemma type_symmetric_univi {o} :
  forall i, @type_symmetric o (univi i).
Proof.
  introv u.
  allrw @univi_exists_iff; exrepnd.
  exists j; sp.
Qed.
Hint Resolve type_symmetric_univi : slow.

Lemma type_extensionality_univi {o} :
  forall i, @type_extensionality o (univi i).
Proof.
  introv u e.
  allrw @univi_exists_iff; exrepnd.
  exists j; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.
Hint Resolve type_extensionality_univi : slow.

Lemma type_transitive_univi {o} :
  forall i, @type_transitive o (univi i).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd.
  spcast; computes_to_eqval.
  exists j0; dands; spcast; auto.
Qed.
Hint Resolve type_transitive_univi : slow.

Lemma type_value_respecting_univi {o} :
  forall i, @type_value_respecting o (univi i).
Proof.
  introv u c.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  pose proof (c _ (lib_extends_refl lib)) as c; simpl in *; spcast.
  eapply cequivc_uni in c;[|eauto].
  exists j; dands; spcast; auto.
Qed.
Hint Resolve type_value_respecting_univi : slow.

Lemma ts_implies_per_bar_univi_bar {o} :
  forall i, @ts_implies_per_bar o (univi_bar i).
Proof.
  introv u.
  unfold univi_bar in *; exrepnd.

  applydup @nuprl_mon_func2.per_bar_monotone_func in u; exrepnd.
  exists (trivial_bar lib) eq'.
  dands.

  { apply in_ext_ext_implies_all_in_bar_ext; introv.
    apply u1. }

  { eapply implies_eq_term_equals_per_bar_eq_trivial_bar_mon; eauto; eauto 3 with slow. }
Qed.
Hint Resolve ts_implies_per_bar_univi_bar : slow.

Lemma term_symmetric_univi_bar {o} :
  forall i,
    (forall m, m < i -> @type_system o (univi_bar m))
    -> @term_symmetric o (univi_bar i).
Proof.
  introv IND u e.
  unfold univi_bar, per_bar in u; exrepnd.
  apply u1 in e; apply u1; clear u1.
  unfold per_bar_eq in *.
  introv br ext; introv.
  pose proof (e _ br _ ext x) as e; simpl in *; exrepnd.
  exists bar'.
  introv br' ext'; introv.
  pose proof (e0 _ br' _ ext' x0) as e0; simpl in *.

  pose proof (u0 _ br lib'2 (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as u0; simpl in *.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in e0; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  apply close_type_symmetric; eauto 3 with slow.
Qed.
Hint Resolve term_symmetric_univi_bar : slow.

Lemma term_transitive_univi_bar {o} :
  forall i,
    (forall m, m < i -> @type_system o (univi_bar m))
    -> @term_transitive o (univi_bar i).
Proof.
  introv IND u e f.
  unfold univi_bar, per_bar in u; exrepnd.
  apply u1 in e; apply u1 in f; apply u1; clear u1.
  unfold per_bar_eq in *.
  introv br ext; introv.
  pose proof (e _ br _ ext x) as e; simpl in *; exrepnd.
  pose proof (f _ br _ ext x) as f; simpl in *; exrepnd.
  exists (intersect_bars bar' bar'0).
  introv br' ext'; introv; simpl in *; exrepnd.
  pose proof (e0 _ br'0 _ (lib_extends_trans ext' br'3) x0) as e0; simpl in *.
  pose proof (f0 _ br'2 _ (lib_extends_trans ext' br'1) x0) as f0; simpl in *.

  pose proof (u0 _ br lib'2 (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as u0; simpl in *.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in e0; apply u1 in f0; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  eapply close_type_transitive; eauto; eauto 3 with slow.
  eapply close_type_extensionality; eauto 2 with slow.

  assert (close (univi_bar j) lib'2 t2 t2 eqa1) as h1.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  assert (close (univi_bar j) lib'2 t2 t2 eqa0) as h2.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  eapply close_uniquely_valued in h1; eauto 3 with slow.
Qed.
Hint Resolve term_transitive_univi_bar : slow.

Lemma term_value_respecting_univi_bar {o} :
  forall i,
    (forall m, m < i -> @type_system o (univi_bar m))
    -> @term_value_respecting o (univi_bar i).
Proof.
  introv IND u e c.
  unfold univi_bar, per_bar in u; exrepnd.
  apply u1 in e; apply u1; clear u1.
  unfold per_bar_eq in *.
  introv br ext; introv.
  pose proof (e _ br _ ext x) as e; simpl in *; exrepnd.
  exists bar'.
  introv br' ext'; introv.
  pose proof (e0 _ br' _ ext' x0) as e0; simpl in *.

  pose proof (u0 _ br lib'2 (lib_extends_trans x0 ext) (lib_extends_trans x0 x)) as u0; simpl in *.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in e0; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  eapply close_type_value_respecting; eauto 3 with slow.
Qed.
Hint Resolve term_value_respecting_univi_bar : slow.

Lemma univi_bar_type_system {o} :
  forall (i : nat), @type_system o (univi_bar i).
Proof.
  induction i using comp_ind_type.
  unfold type_system; dands; eauto 2 with slow.

  - eapply uniquely_valued_per_bar; eauto 3 with slow.

  - apply type_symmetric_per_bar; eauto 3 with slow.

  - apply type_transitive_per_bar; eauto 3 with slow.

  - apply type_value_respecting_per_bar; eauto 3 with slow.
Qed.
Hint Resolve univi_bar_type_system : slow.

Lemma term_symmetric_univi {o} :
  forall i, @term_symmetric o (univi i).
Proof.
  introv u e.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in e; apply u0; clear u0.
  unfold univi_eq in *; exrepnd.
  exists eqa.
  eapply close_type_symmetric; eauto 3 with slow.
Qed.
Hint Resolve term_symmetric_univi : slow.

Lemma term_transitive_univi {o} :
  forall i, @term_transitive o (univi i).
Proof.
  introv u e f.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in e; apply u0 in f; apply u0; clear u0.
  unfold univi_eq in *; exrepnd.
  exists eqa.
  eapply close_type_transitive; eauto 3 with slow.
  eapply close_type_extensionality; eauto 2 with slow.

  assert (close (univi_bar j) lib t2 t2 eqa0) as h1.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  assert (close (univi_bar j) lib t2 t2 eqa) as h2.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  eapply close_uniquely_valued in h1; eauto 3 with slow.
Qed.
Hint Resolve term_transitive_univi : slow.

Lemma term_value_respecting_univi {o} :
  forall i, @term_value_respecting o (univi i).
Proof.
  introv u e c.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in e; apply u0; clear u0.
  unfold univi_eq in *; exrepnd.
  exists eqa.
  eapply close_type_value_respecting; eauto 3 with slow.
Qed.
Hint Resolve term_value_respecting_univi : slow.

Lemma univi_type_system {o} :
  forall (i : nat), @type_system o (univi i).
Proof.
  introv; unfold type_system; dands; eauto 3 with slow.
Qed.
Hint Resolve univi_type_system : slow.

(* begin hide *)

Lemma nuprli_type_system {o} :
  forall (i : nat), @type_system o (nuprli i).
Proof.
  unfold nuprli; sp.
  apply close_type_system; eauto 3 with slow.
Qed.
Hint Resolve nuprli_type_system : slow.

Lemma nuprli_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    nuprli i1 lib T T' eq
    -> nuprli i2 lib T T' eq'
    -> eq <=2=> eq'.
Proof.
  sp.
  assert (nuprli (i2 + i1) lib T T' eq) as c1 by (apply typable_in_higher_univ; auto).
  assert (nuprli (i1 + i2) lib T T' eq') as c2 by (apply typable_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  generalize (@nuprli_type_system o (i2 + i1)); intro nts.
  destruct nts; sp.
  unfold uniquely_valued in u.
  eapply u; eauto.
Qed.

Lemma nuprli_type_transitive {o} :
  forall lib i1 i2 (T1 T2 T3 : @CTerm o) eq,
    nuprli i1 lib T1 T2 eq
    -> nuprli i2 lib T2 T3 eq
    -> {i : nat & nuprli i lib T1 T3 eq # i1 <= i # i2 <= i}.
Proof.
  sp.
  assert (nuprli (i1 + i2) lib T1 T2 eq) as c1 by (apply typable_in_higher_univ_r; auto).
  assert (nuprli (i1 + i2) lib T2 T3 eq) as c2 by (apply typable_in_higher_univ; auto).
  exists (i1 + i2); sp; try omega.
  generalize (@nuprli_type_system o (i1 + i2)); intro nts.
  destruct nts; sp.
  apply p2 with (T2 := T2); sp.
Qed.

Lemma univi_uniquely_valued {o} :
  forall lib i1 i2 (T T' : @CTerm o) eq eq',
    univi i1 lib T T' eq
    -> univi i2 lib T T' eq'
    -> eq <=2=> eq'.
Proof.
  introv u v.
  assert (univi (i2 + i1) lib T T' eq) as c1 by (apply uni_in_higher_univ; auto).
  assert (univi (i1 + i2) lib T T' eq') as c2 by (apply uni_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by omega.
  rww e.
  eapply uniquely_valued_univi; eauto.
Qed.

(* end hide *)


(**

  We prove that that [univ] satisfies the type system properties.

*)

Lemma univ_type_system {o} : @type_system o univ.
Proof.
  unfold univ, type_system; sp.

  - unfold uniquely_valued; sp.
    apply (univi_uniquely_valued lib) with (i1 := i0) (i2 := i) (T := T) (T' := T'); auto.

  - unfold type_extensionality; sp.
    exists i.
    generalize (@univi_type_system o i); intro uts.
    dest_ts uts.
    unfold type_extensionality in ts_ext.
    apply ts_ext with (eq := eq); auto.

  - unfold type_symmetric; sp.
    exists i.
    generalize (@univi_type_system o i); intro uts.
    dest_ts uts; auto.

  - unfold type_transitive; introv u1 u2; exrepnd.
    apply uni_in_higher_univ with (k := i0) in u0.
    apply uni_in_higher_univ_r with (k := i) in u2.
    exists (i0 + i).
    generalize (@univi_type_system o (i0 + i)); intro uts.
    dest_ts uts; auto.
    apply ts_tyt with (T2 := T2); auto.

  - unfold type_value_respecting; sp.
    exists i.
    generalize (@univi_type_system o i); intro uts.
    dest_ts uts; sp.

  - unfold term_symmetric, term_equality_symmetric; introv u e1; exrepnd.
    generalize (@univi_type_system o i); intro uts.
    dest_ts uts; sp.
    apply ts_tes in u0.
    apply u0; auto.

  - unfold term_transitive, term_equality_transitive; introv u e1 e2; exrepnd.
    generalize (@univi_type_system o i); intro uts.
    dest_ts uts; sp.
    apply ts_tet in u0.
    apply u0 with (t2 := t2); auto.

  - unfold term_value_respecting, term_equality_respecting; introv u e1 c1; exrepnd.
    generalize (@univi_type_system o i); intro uts.
    dest_ts uts; sp.
    apply ts_tev in u0.
    apply u0; auto.
Qed.
Hint Resolve univ_type_system : slow.

(**

  Finally, we prove that that [nuprl] satisfies the type system properties.

*)

Lemma nuprl_type_system {p} : @type_system p nuprl.
Proof.
  introv.
  apply close_type_system; eauto 3 with slow.
Qed.
Hint Resolve nuprl_type_system : slow.

(* begin hide *)

(** Here is a tactic to use the fact that nuprl is a type system *)
Ltac nts :=
  match goal with
      [ p : POpid |- _ ] =>
      pose proof (@nuprl_type_system p) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tys nts ];
        destruct nts as [ nts_tyt nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Lemma nuprl_refl {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    nuprl lib t1 t2 eq -> nuprl lib t1 t1 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t2 t1 eq); sp.
  use_trans t2; sp.
Qed.

Lemma nuprl_sym {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    nuprl lib t1 t2 eq -> nuprl lib t2 t1 eq.
Proof.
  intros; nts; sp.
Qed.

Lemma nuprl_trans {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq1 eq2,
    nuprl lib t1 t2 eq1 -> nuprl lib t2 t3 eq2 -> nuprl lib t1 t3 eq1.
Proof.
  introv n1 n2; nts.
  use_trans t2; sp.
  use_ext eq2; sp.
  eapply uniquely_valued_eq; eauto.
Qed.

Lemma nuprl_uniquely_valued {p} :
  forall lib (t : @CTerm p) eq1 eq2,
    nuprl lib t t eq1
    -> nuprl lib t t eq2
    -> eq_term_equals eq1 eq2.
Proof.
  introv n1 n2; nts.
  eapply nts_uv; eauto.
Qed.

Lemma nuprl_value_respecting_left {p} :
  forall lib (t1 t2 t3 : @CTerm p) eq,
    nuprl lib t1 t2 eq
    -> ccequivc_ext lib t1 t3
    -> nuprl lib t3 t2 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t1 t3 eq) as eq13
    by (apply nts_tyv; auto; eapply nts_tyt; eauto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprl_value_respecting_right {p} :
  forall lib t1 t2 t3 eq,
    @nuprl p lib t1 t2 eq
    -> ccequivc_ext lib t2 t3
    -> nuprl lib t1 t3 eq.
Proof.
  intros.
  nts.
  assert (nuprl lib t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Lemma nuprl_eq_implies_eqorceq_refl {p} :
  forall lib T1 T2 eq t1 t2,
    @nuprl p lib T1 T2 eq
    -> eq t1 t2
    -> eqorceq lib eq t1 t1 # eqorceq lib eq t2 t2.
Proof.
  introv n e.
  nts; sp; left.

  { unfold term_transitive, term_equality_transitive in nts_tet.
    eapply nts_tet; eauto.
    unfold term_symmetric, term_equality_symmetric in nts_tes.
    eapply nts_tes; eauto. }

  { unfold term_transitive, term_equality_transitive in nts_tet.
    eapply nts_tet; eauto.
    unfold term_symmetric, term_equality_symmetric in nts_tes.
    eapply nts_tes; eauto. }
Qed.

(* end hide *)
