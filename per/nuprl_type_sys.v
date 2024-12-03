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
  forall lib (T : @CTerm o) u i,
    ccomputes_to_valc_ext lib T (mkc_uni u i)
    -> computes_to_uni u lib T.
Proof.
  introv comp.
  apply in_ext_implies_in_open_bar; introv ext.
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
  eapply in_open_bar_comb2; eauto; clear u1.
  apply in_ext_ext_implies_in_open_bar_ext; introv u1.
  allrw @univi_exists_iff; exrepnd.
  exists j; auto.
Qed.
Hint Resolve defines_only_universes_univi_bar : slow.

Lemma defines_only_universes_univ {o} :
  @defines_only_universes o univ.
Proof.
  unfold defines_only_universes, univ, univ_ex; introv per.
  unfold per_bar in *; exrepnd.
  eapply in_open_bar_comb2; eauto; clear per1.
  apply in_ext_ext_implies_in_open_bar_ext; introv u1; exrepnd.
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
  forall lib (T T' : @CTerm o) u i,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc lib T (mkc_uni u i)
    -> ccomputes_to_valc lib T' (mkc_uni u i).
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_uni in ceq';[|eauto]; exrepnd; auto.
Qed.

Lemma per_bar_univi_uniquely_valued {o} :
  forall i uk lib (T T' : @CTerm o) eq1 eq2,
    per_bar (univi i) uk lib T T' eq1
    -> per_bar (univi i) uk lib T T' eq2
    -> eq1 <=2=> eq2.
Proof.
  introv u v.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  unfold per_bar_eq; introv; split; intro h.

  - eapply in_open_bar_ext_comb; try exact u1; clear u1.
    eapply in_open_bar_ext_comb; try exact v1; clear v1.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h v1 u1.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_eqval_ext.
    apply ccequivc_ext_uni_uni_implies in ceq; repnd; subst.
    apply v2; apply u2; auto.

  - eapply in_open_bar_ext_comb; try exact u1; clear u1.
    eapply in_open_bar_ext_comb; try exact v1; clear v1.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h v1 u1.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_eqval_ext.
    apply ccequivc_ext_uni_uni_implies in ceq; repnd; subst.
    apply u2; apply v2; auto.
Qed.

Lemma uniquely_valued_univi {o} :
  forall i, @uniquely_valued o (univi i).
Proof.
  introv u v.
  allrw @univi_exists_iff; exrepnd; spcast.
  computes_to_eqval_ext.
  apply ccequivc_ext_uni_uni_implies in ceq; repnd; subst.
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
  spcast; computes_to_eqval_ext.
  apply ccequivc_ext_uni_uni_implies in ceq; repnd; subst.
  exists j0; dands; spcast; auto.
Qed.
Hint Resolve type_transitive_univi : slow.

Lemma type_value_respecting_univi {o} :
  forall i, @type_value_respecting o (univi i).
Proof.
  introv u c.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  exists j; dands; eauto 3 with slow.
Qed.
Hint Resolve type_value_respecting_univi : slow.

Lemma ts_implies_per_bar_univi_bar {o} :
  forall i, @ts_implies_per_bar o (univi_bar i).
Proof.
  introv u.
  unfold univi_bar in *; exrepnd.

  applydup @per_bar_monotone_func2 in u; exrepnd.
  exists eq'.
  dands.

  { apply in_ext_ext_implies_in_open_bar_ext; introv.
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
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; eauto; clear e; introv h u1.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in h; apply u0; clear u0.
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
  apply u0 in e; apply u0 in f; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_comb; try exact e; clear e.
  eapply in_open_bar_ext_pres; try exact f; clear f; introv f h u1.

  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in h; apply u0 in f; apply u0; clear u0.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  eapply close_type_transitive; eauto; eauto 3 with slow.
  eapply close_type_extensionality; eauto 2 with slow.

  assert (close (univi_bar j) uk lib' t2 t2 eqa1) as h1.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  assert (close (univi_bar j) uk lib' t2 t2 eqa0) as h2.
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
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; try exact e; clear e; introv h u1.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u0 in h; apply u0; clear u0.
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

  assert (close (univi_bar j) uk lib t2 t2 eqa0) as h1.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  assert (close (univi_bar j) uk lib t2 t2 eqa) as h2.
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
  forall uk lib i1 i2 (T T' : @CTerm o) eq eq',
    nuprli i1 uk lib T T' eq
    -> nuprli i2 uk lib T T' eq'
    -> eq <=2=> eq'.
Proof.
  sp.
  assert (nuprli (i2 + i1) uk lib T T' eq) as c1 by (apply typable_in_higher_univ; auto).
  assert (nuprli (i1 + i2) uk lib T T' eq') as c2 by (apply typable_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by lia.
  rww e.
  generalize (@nuprli_type_system o (i2 + i1)); intro nts.
  destruct nts; sp.
  unfold uniquely_valued in u.
  eapply u; eauto.
Qed.

Lemma nuprli_type_transitive {o} :
  forall uk lib i1 i2 (T1 T2 T3 : @CTerm o) eq,
    nuprli i1 uk lib T1 T2 eq
    -> nuprli i2 uk lib T2 T3 eq
    -> {i : nat & nuprli i uk lib T1 T3 eq # i1 <= i # i2 <= i}.
Proof.
  sp.
  assert (nuprli (i1 + i2) uk lib T1 T2 eq) as c1 by (apply typable_in_higher_univ_r; auto).
  assert (nuprli (i1 + i2) uk lib T2 T3 eq) as c2 by (apply typable_in_higher_univ; auto).
  exists (i1 + i2); sp; try lia.
  generalize (@nuprli_type_system o (i1 + i2)); intro nts.
  destruct nts; sp.
  apply p2 with (T2 := T2); sp.
Qed.

Lemma univi_uniquely_valued {o} :
  forall uk lib i1 i2 (T T' : @CTerm o) eq eq',
    univi i1 uk lib T T' eq
    -> univi i2 uk lib T T' eq'
    -> eq <=2=> eq'.
Proof.
  introv u v.
  assert (univi (i2 + i1) uk lib T T' eq) as c1 by (apply uni_in_higher_univ; auto).
  assert (univi (i1 + i2) uk lib T T' eq') as c2 by (apply uni_in_higher_univ; auto).
  assert (i1 + i2 = i2 + i1) as e by lia.
  rww e.
  eapply uniquely_valued_univi; eauto.
Qed.

(* end hide *)


(**

  We prove that that [univ] satisfies the type system properties.

 *)

Lemma type_symmetric_univ_ex {o} :
  @type_symmetric o univ_ex.
Proof.
  introv u.
  unfold univ_ex in *; exrepnd.
  exists i.
  apply type_symmetric_univi; auto.
Qed.
Hint Resolve type_symmetric_univ_ex : slow.

Lemma type_transitive_univ_ex {o} :
  @type_transitive o univ_ex.
Proof.
  introv u v.
  unfold univ_ex in *; exrepnd.
  assert (univi (i + i0) uk lib T1 T2 eq) as c1 by (apply uni_in_higher_univ; auto).
  assert (univi (i0 + i) uk lib T2 T3 eq) as c2 by (apply uni_in_higher_univ; auto).
  assert (i + i0 = i0 + i) as e by lia.
  rewrite e in c1; clear e.

  exists (i0 + i).
  eapply type_transitive_univi; eauto.
Qed.
Hint Resolve type_transitive_univ_ex : slow.

Lemma type_value_respecting_univ_ex {o} :
  @type_value_respecting o univ_ex.
Proof.
  introv u.
  unfold univ_ex in *; exrepnd.
  exists i.
  apply type_value_respecting_univi; auto.
Qed.
Hint Resolve type_value_respecting_univ_ex : slow.

Lemma term_symmetric_univ {o} :
  @term_symmetric o univ.
Proof.
  introv u e.
  unfold univ, per_bar in u; exrepnd.
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; try exact e; clear e; introv h u1.
  unfold univ_ex in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in h; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  apply close_type_symmetric; eauto 3 with slow.
Qed.
Hint Resolve term_symmetric_univ : slow.

Lemma term_transitive_univ {o} :
  @term_transitive o univ.
Proof.
  introv u e f.
  unfold univ, per_bar in u; exrepnd.
  apply u0 in e; apply u0 in f; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_comb; try exact e; clear e.
  eapply in_open_bar_ext_pres; try exact f; clear f; introv f h u1.

  unfold univ_ex in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in h; apply u1 in f; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  eapply close_type_transitive; eauto; eauto 3 with slow.
  eapply close_type_extensionality; eauto 2 with slow.

  assert (close (univi_bar j) uk lib' t2 t2 eqa1) as h1.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  assert (close (univi_bar j) uk lib' t2 t2 eqa0) as h2.
  { eapply close_type_transitive; eauto; eauto 3 with slow.
    eapply close_type_symmetric; eauto; eauto 3 with slow. }

  eapply close_uniquely_valued in h1; eauto 3 with slow.
Qed.
Hint Resolve term_transitive_univ : slow.

Lemma term_value_respecting_univ {o} :
  @term_value_respecting o univ.
Proof.
  introv u e c.
  unfold univ, per_bar in u; exrepnd.
  apply u0 in e; apply u0; clear u0.
  unfold per_bar_eq in *.
  eapply in_open_bar_ext_comb; try exact u1; clear u1.
  eapply in_open_bar_ext_pres; try exact e; clear e; introv h u1.

  unfold univ_ex in *; exrepnd.
  allrw @univi_exists_iff; exrepnd.
  spcast.
  apply u1 in h; apply u1; clear u1.
  unfold univi_eq in *; exrepnd.
  exists eqa0.

  eapply close_type_value_respecting; eauto 3 with slow.
Qed.
Hint Resolve term_value_respecting_univ : slow.

Lemma univ_type_system {o} : @type_system o univ.
Proof.
  unfold type_system; dands; eauto 3 with slow.

  - eapply uniquely_valued_per_bar; eauto 3 with slow.

  - apply type_symmetric_per_bar; eauto 3 with slow.

  - apply type_transitive_per_bar; eauto 3 with slow.

  - apply type_value_respecting_per_bar; eauto 3 with slow.
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
  forall uk lib (t1 t2 : @CTerm p) eq,
    nuprl uk lib t1 t2 eq -> nuprl uk lib t1 t1 eq.
Proof.
  intros.
  nts.
  assert (nuprl uk lib t2 t1 eq); sp.
  use_trans t2; sp.
Qed.

Lemma nuprl_sym {p} :
  forall uk lib (t1 t2 : @CTerm p) eq,
    nuprl uk lib t1 t2 eq -> nuprl uk lib t2 t1 eq.
Proof.
  intros; nts; sp.
Qed.

Lemma nuprl_trans {p} :
  forall uk lib (t1 t2 t3 : @CTerm p) eq1 eq2,
    nuprl uk lib t1 t2 eq1 -> nuprl uk lib t2 t3 eq2 -> nuprl uk lib t1 t3 eq1.
Proof.
  introv n1 n2; nts.
  use_trans t2; sp.
  use_ext eq2; sp.
  eapply uniquely_valued_eq; eauto.
Qed.

Lemma nuprl_uniquely_valued {p} :
  forall uk lib (t : @CTerm p) eq1 eq2,
    nuprl uk lib t t eq1
    -> nuprl uk lib t t eq2
    -> eq_term_equals eq1 eq2.
Proof.
  introv n1 n2; nts.
  eapply nts_uv; eauto.
Qed.

Lemma nuprl_value_respecting_left {p} :
  forall uk lib (t1 t2 t3 : @CTerm p) eq,
    nuprl uk lib t1 t2 eq
    -> ccequivc_ext lib t1 t3
    -> nuprl uk lib t3 t2 eq.
Proof.
  intros.
  nts.
  assert (nuprl uk lib t1 t3 eq) as eq13
    by (apply nts_tyv; auto; eapply nts_tyt; eauto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprl_value_respecting_right {p} :
  forall uk lib t1 t2 t3 eq,
    @nuprl p uk lib t1 t2 eq
    -> ccequivc_ext lib t2 t3
    -> nuprl uk lib t1 t3 eq.
Proof.
  intros.
  nts.
  assert (nuprl uk lib t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Ltac ntsi :=
  match goal with
    [ o : POpid , H : nuprli ?i _ _ _ _ _ |- _ ] =>
    pose proof (@nuprli_type_system o i) as nts;
    destruct nts as [ nts_uv nts ];
    destruct nts as [ nts_ext nts ];
    destruct nts as [ nts_tys nts ];
    destruct nts as [ nts_tyt nts ];
    destruct nts as [ nts_tyv nts ];
    destruct nts as [ nts_tes nts ];
    destruct nts as [ nts_tet nts_tev ]
  end.

Lemma nuprli_value_respecting_left {o} :
  forall i uk lib (t1 t2 t3 : @CTerm o) eq,
    nuprli i uk lib t1 t2 eq
    -> ccequivc_ext lib t1 t3
    -> nuprli i uk lib t3 t2 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli i uk lib t1 t3 eq) as eq13
    by (apply nts_tyv; auto; eapply nts_tyt; eauto).
  apply nts_tyt with (T2 := t1); auto.
Qed.

Lemma nuprli_value_respecting_right {o} :
  forall i uk lib (t1 t2 t3 : @CTerm o) eq,
    nuprli i uk lib t1 t2 eq
    -> ccequivc_ext lib t2 t3
    -> nuprli i uk lib t1 t3 eq.
Proof.
  intros.
  ntsi.
  assert (nuprli i uk lib t2 t3 eq) as eq23
    by (apply nts_tyv; auto; apply nts_tyt with (T2 := t1); auto).
  apply nts_tyt with (T2 := t2); auto.
Qed.

Lemma in_ext_ext_nuprli_value_respecting_left {o} :
  forall i uk lib (t1 t2 t3 : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprli i uk lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t1 t3
    -> in_ext_ext lib (fun lib x => nuprli i uk lib t3 t2 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprli_value_respecting_right {o} :
  forall i uk lib (t1 t2 t3 : @CTerm o) eq,
    in_ext_ext lib (fun lib x => nuprli i uk lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t2 t3
    -> in_ext_ext lib (fun lib x => nuprli i uk lib t1 t3 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprli_value_respecting_left {o} :
  forall i uk lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i uk lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v1] t1 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i uk lib (substc a v3 t3) (substc a' v2 t2) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprli_value_respecting_right {o} :
  forall i uk lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i uk lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v2] t2 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprli i uk lib (substc a v1 t1) (substc a' v3 t3) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprli_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprl_value_respecting_left {o} :
  forall uk lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl uk lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v1] t1 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl uk lib (substc a v3 t3) (substc a' v2 t2) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_fam_nuprl_value_respecting_right {o} :
  forall uk lib v1 v2 v3 (t1 : @CVTerm o [v1]) t2 t3 eqa (eq : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl uk lib (substc a v1 t1) (substc a' v2 t2) (eq lib x a a' e))
    -> bcequivc_ext lib [v2] t2 [v3] t3
    -> in_ext_ext lib (fun lib x => forall a a' (e : eqa lib x a a'), nuprl uk lib (substc a v1 t1) (substc a' v3 t3) (eq lib x a a' e)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprl_value_respecting_left {o} :
  forall uk lib (t1 t2 t3 : @CTerm o) (eq : lib-per(lib,o)),
    in_ext_ext lib (fun lib x => nuprl uk lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t1 t3
    -> in_ext_ext lib (fun lib x => nuprl uk lib t3 t2 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_left;[eauto|]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_nuprl_value_respecting_right {o} :
  forall uk lib (t1 t2 t3 : @CTerm o) eq,
    in_ext_ext lib (fun lib x => nuprl uk lib t1 t2 (eq lib x))
    -> ccequivc_ext lib t2 t3
    -> in_ext_ext lib (fun lib x => nuprl uk lib t1 t3 (eq lib x)).
Proof.
  introv h ceq; introv.
  pose proof (h _ e) as h; simpl in h.
  eapply nuprl_value_respecting_right;[eauto|]; eauto 3 with slow.
Qed.

Lemma nuprl_eq_implies_eqorceq_refl {p} :
  forall uk lib T1 T2 eq t1 t2,
    @nuprl p uk lib T1 T2 eq
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

Lemma in_ext_ext_nuprl_implies_in_ext_ext_term_equality_respecting {o} :
  forall uk lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprl uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  nts; auto.
  eapply term_reduces_to_symm; eauto.
Qed.
Hint Resolve in_ext_ext_nuprl_implies_in_ext_ext_term_equality_respecting : slow.

Lemma in_ext_ext_nuprl_implies_in_ext_ext_term_equality_transitive {o} :
  forall uk lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprl uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  nts; auto.
  apply nts_tet in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprl_implies_in_ext_ext_term_equality_transitive : slow.

Lemma in_ext_ext_nuprl_implies_in_ext_ext_term_equality_symmetric {o} :
  forall uk lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprl uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  nts; auto.
  apply nts_tes in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprl_implies_in_ext_ext_term_equality_symmetric : slow.

Lemma in_ext_ext_nuprli_implies_in_ext_ext_term_equality_respecting {o} :
  forall i uk lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprli i uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  apply nuprli_implies_nuprl in h.
  nts; auto.
  eapply term_reduces_to_symm; eauto.
Qed.
Hint Resolve in_ext_ext_nuprli_implies_in_ext_ext_term_equality_respecting : slow.

Lemma in_ext_ext_nuprli_implies_in_ext_ext_term_equality_transitive {o} :
  forall i uk lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprli i uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  apply nuprli_implies_nuprl in h.
  nts; auto.
  apply nts_tet in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprli_implies_in_ext_ext_term_equality_transitive : slow.

Lemma in_ext_ext_nuprli_implies_in_ext_ext_term_equality_symmetric {o} :
  forall i uk lib (eqa : lib-per(lib,o)) A B,
    in_ext_ext lib (fun lib' x => nuprli i uk lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x)).
Proof.
  introv h; introv.
  pose proof (h _ e) as h; simpl in h.
  apply nuprli_implies_nuprl in h.
  nts; auto.
  apply nts_tes in h; auto.
Qed.
Hint Resolve in_ext_ext_nuprli_implies_in_ext_ext_term_equality_symmetric : slow.

(* end hide *)
